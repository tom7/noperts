// OpenCL version of TILT_GRAD method, for use in tiltperts.cc.

#pragma OPENCL EXTENSION cl_khr_fp64 : enable

#ifndef NUM_VERTICES
#error "NUM_VERTICES must be defined"
#endif

#define MAX_EDGES 32

typedef struct {
  double2 normal; // 16 bytes
  double b;       // 8 bytes
  double _pad;    // 8 bytes
} GpuEdge;

typedef struct {
  double4 q_outer;          // 32 bytes
  int num_edges;            // 4 bytes
  int _pad[7];              // 28 bytes -> 32 bytes
  GpuEdge edges[MAX_EDGES]; // 32 * 32 = 1024 bytes
} GpuOuterPose;



typedef struct {
  int solved;         // 4 bytes
  int outer_idx;      // 4 bytes
  int _pad[6];        // 24 bytes -> 32 bytes
  double4 q_outer;    // 32 bytes
  double4 w_inner;    // 32 bytes (w.x, w.y, w.z, 0.0)
  double2 t_inner;    // 16 bytes
  double clearance;   // 8 bytes
  double _pad2;       // 8 bytes -> 32 bytes
} GpuSolution;

typedef struct {
  double clearance;   // 8 bytes
  double _pad;        // 8 bytes
  double2 t_inner;    // 16 bytes -> 32 bytes
  double4 w_inner;    // 32 bytes
} GpuCandidate;

inline double4 QuatNormalize(double4 q) {
  double len = sqrt(q.x * q.x + q.y * q.y + q.z * q.z + q.w * q.w);
  if (len < 1e-15) return (double4)(0.0, 0.0, 0.0, 1.0);
  return q / len;
}

inline double4 QuatMul(double4 q1, double4 q2) {
  return (double4)(
    q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y,
    q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x,
    q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w,
    q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z
  );
}

// Convert rotation vector w in R^3 to unit quaternion exp(w / 2)
inline double4 RotationVectorToQuat(double3 w) {
  double theta = length(w);
  if (theta < 1e-12) {
    return (double4)(0.0, 0.0, 0.0, 1.0);
  }
  double s = sin(theta * 0.5) / theta;
  return (double4)(s * w.x, s * w.y, s * w.z, cos(theta * 0.5));
}

// Rotate vector v by unit quaternion q: v' = q * (v, 0) * q^-1
inline double3 QuatRotateVector(double4 q, double3 v) {
  double3 qv = q.xyz;
  double3 t = 2.0 * cross(qv, v);
  return v + q.w * t + cross(qv, t);
}

// Computes edge offset margins d_j = max_k (b_j - mu_j ∙ v_k) using dual support identity
inline void ComputeEdgeOffsets(
    __constant const double *base_verts,
    __local const GpuEdge *edges,
    int num_edges,
    double4 q_inner,
    double *d) {
  // Inverse rotation of inner frame: q_inv = (-x, -y, -z, w)
  double4 q_inv = (double4)(-q_inner.x, -q_inner.y, -q_inner.z, q_inner.w);

  for (int j = 0; j < num_edges; j++) {
    double3 n_3d = (double3)(edges[j].normal.x, edges[j].normal.y, 0.0);
    double3 mu = QuatRotateVector(q_inv, n_3d);

    double max_val = -1e30;
    for (int k = 0; k < NUM_VERTICES; k++) {
      double3 vk = (double3)(base_verts[k * 3 + 0],
                             base_verts[k * 3 + 1],
                             base_verts[k * 3 + 2]);
      double val = edges[j].b - dot(mu, vk);
      if (val > max_val) max_val = val;
    }
    d[j] = max_val;
  }
}

inline double EvalClearanceAtT(
    __local const GpuEdge *edges,
    int num_edges,
    const double *d,
    double2 t) {
  double min_c = 1e30;
  for (int j = 0; j < num_edges; j++) {
    double cj = dot(edges[j].normal, t) - d[j];
    if (cj < min_c) min_c = cj;
  }
  return min_c;
}

// 2D Nelder-Mead simplex optimization to maximize min_j (n_j ∙ t - d_j)
inline double MaximizeClearance2D_NM(
    __local const GpuEdge *edges,
    int num_edges,
    const double *d,
    double2 initial_t,
    double initial_step,
    double2 *best_t) {
  double2 p[3];
  double f[3];

  p[0] = initial_t;
  p[1] = initial_t + (double2)(initial_step, 0.0);
  p[2] = initial_t + (double2)(0.0, initial_step);

  f[0] = -EvalClearanceAtT(edges, num_edges, d, p[0]);
  f[1] = -EvalClearanceAtT(edges, num_edges, d, p[1]);
  f[2] = -EvalClearanceAtT(edges, num_edges, d, p[2]);

  for (int iter = 0; iter < 24; iter++) {
    // Sort so f[0] <= f[1] <= f[2]
    if (f[0] > f[1]) {
      double tf = f[0]; f[0] = f[1]; f[1] = tf;
      double2 tp = p[0]; p[0] = p[1]; p[1] = tp;
    }
    if (f[1] > f[2]) {
      double tf = f[1]; f[1] = f[2]; f[2] = tf;
      double2 tp = p[1]; p[1] = p[2]; p[2] = tp;
    }
    if (f[0] > f[1]) {
      double tf = f[0]; f[0] = f[1]; f[1] = tf;
      double2 tp = p[0]; p[0] = p[1]; p[1] = tp;
    }

    double2 c = (p[0] + p[1]) * 0.5;

    // Reflection
    double2 xr = 2.0 * c - p[2];
    double fr = -EvalClearanceAtT(edges, num_edges, d, xr);

    if (fr < f[0]) {
      // Expansion
      double2 xe = c + 2.0 * (xr - c);
      double fe = -EvalClearanceAtT(edges, num_edges, d, xe);
      if (fe < fr) {
        p[2] = xe; f[2] = fe;
      } else {
        p[2] = xr; f[2] = fr;
      }
    } else if (fr < f[1]) {
      p[2] = xr; f[2] = fr;
    } else {
      // Contraction
      if (fr < f[2]) {
        // Outside contraction
        double2 xc = c + 0.5 * (xr - c);
        double fc = -EvalClearanceAtT(edges, num_edges, d, xc);
        if (fc <= fr) {
          p[2] = xc; f[2] = fc;
        } else {
          // Shrink towards p[0]
          p[1] = p[0] + 0.5 * (p[1] - p[0]);
          p[2] = p[0] + 0.5 * (p[2] - p[0]);
          f[1] = -EvalClearanceAtT(edges, num_edges, d, p[1]);
          f[2] = -EvalClearanceAtT(edges, num_edges, d, p[2]);
        }
      } else {
        // Inside contraction
        double2 xc = c - 0.5 * (c - p[2]);
        double fc = -EvalClearanceAtT(edges, num_edges, d, xc);
        if (fc < f[2]) {
          p[2] = xc; f[2] = fc;
        } else {
          // Shrink towards p[0]
          p[1] = p[0] + 0.5 * (p[1] - p[0]);
          p[2] = p[0] + 0.5 * (p[2] - p[0]);
          f[1] = -EvalClearanceAtT(edges, num_edges, d, p[1]);
          f[2] = -EvalClearanceAtT(edges, num_edges, d, p[2]);
        }
      }
    }
  }

  int best_idx = 0;
  if (f[1] < f[best_idx]) best_idx = 1;
  if (f[2] < f[best_idx]) best_idx = 2;

  *best_t = p[best_idx];
  return -f[best_idx];
}

inline double EvalClearanceForW(
    __constant const double *base_verts,
    __local const GpuEdge *edges,
    int num_edges,
    double4 q_outer,
    double3 w,
    double2 initial_t,
    double initial_step,
    double2 *out_t) {
  double4 delta_q = RotationVectorToQuat(w);
  double4 q_inner = QuatNormalize(QuatMul(delta_q, q_outer));

  double d[MAX_EDGES];
  ComputeEdgeOffsets(base_verts, edges, num_edges, q_inner, d);

  return MaximizeClearance2D_NM(edges, num_edges, d, initial_t, initial_step, out_t);
}

__kernel void TiltGradAscent(
    __constant const double *base_verts,
    __global const GpuOuterPose *outer_poses,
    int max_steps,
    __global GpuSolution *solution,
    __global GpuCandidate *candidates) {

  __local GpuEdge local_edges[MAX_EDGES];
  __local int local_num_edges;
  __local double4 local_q_outer;

  int lid = get_local_id(0);
  int gid = get_group_id(0);
  int lsize = get_local_size(0);

  if (lid == 0) {
    local_num_edges = outer_poses[gid].num_edges;
    local_q_outer = outer_poses[gid].q_outer;
  }
  if (lid < MAX_EDGES) {
    local_edges[lid] = outer_poses[gid].edges[lid];
  }
  barrier(CLK_LOCAL_MEM_FENCE);

  if (local_num_edges < 3) return;

  // Initial candidate exploration: 3D tilt directions across 4 radial scales
  int num_scales = 4;
  int dirs_per_scale = max(1, lsize / num_scales);
  int scale_idx = lid / dirs_per_scale;
  int dir_idx = lid % dirs_per_scale;

  double scales[4] = { 0.0008, 0.002, 0.008, 0.025 };
  double r = scales[min(scale_idx, 3)];

  // Fibonacci sphere distribution for uniform unit vectors on S^2 in R^3
  double z_coord = 1.0 - 2.0 * ((double)dir_idx + 0.5) / (double)dirs_per_scale;
  double r_xy = sqrt(max(0.0, 1.0 - z_coord * z_coord));
  double phi = (double)dir_idx * 2.399963229728653;
  double3 u = (double3)(r_xy * cos(phi), r_xy * sin(phi), z_coord);
  double3 w = r * u;



  double2 best_t = (double2)(0.0, 0.0);
  double c = EvalClearanceForW(base_verts, local_edges, local_num_edges,
                              local_q_outer, w, best_t, 0.0005, &best_t);

  double3 best_w = w;
  double best_c = c;

  if (best_c > 1e-10 && length(best_w) > 1e-8) {
    if (atomic_cmpxchg((volatile __global int *)&solution->solved, 0, 1) == 0) {
      solution->outer_idx = gid;
      solution->q_outer = local_q_outer;
      solution->w_inner = (double4)(best_w.x, best_w.y, best_w.z, 0.0);
      solution->t_inner = best_t;
      solution->clearance = best_c;
    }
  }

  // Backtracking Gradient Ascent on 3D tilt vector (w_x, w_y, w_z)
  const double EPS = 1e-5;
  double step_size = 5e-4;

  for (int iter = 0; iter < max_steps; iter++) {
    if (solution->solved) break;
    if (best_c > 1e-9) break;

    double2 dummy_t;
#ifdef FORWARD_DIFFERENCE
    // Forward difference gradient in 3D (3 evaluations using best_c = c(w)):
    double cx_p =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w + (double3)(EPS, 0.0, 0.0), best_t, 1e-5, &dummy_t);
    double cy_p =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w + (double3)(0.0, EPS, 0.0), best_t, 1e-5, &dummy_t);
    double cz_p =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w + (double3)(0.0, 0.0, EPS), best_t, 1e-5, &dummy_t);

    double3 grad = (double3)(
      (cx_p - best_c) / EPS,
      (cy_p - best_c) / EPS,
      (cz_p - best_c) / EPS
    );
#else
    // Central difference gradient in 3D (6 evaluations):
    double cx_p =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w + (double3)(EPS, 0.0, 0.0), best_t, 1e-5, &dummy_t);
    double cx_m =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w - (double3)(EPS, 0.0, 0.0), best_t, 1e-5, &dummy_t);

    double cy_p =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w + (double3)(0.0, EPS, 0.0), best_t, 1e-5, &dummy_t);
    double cy_m =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w - (double3)(0.0, EPS, 0.0), best_t, 1e-5, &dummy_t);

    double cz_p =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w + (double3)(0.0, 0.0, EPS), best_t, 1e-5, &dummy_t);
    double cz_m =
      EvalClearanceForW(base_verts, local_edges, local_num_edges,
                        local_q_outer, w - (double3)(0.0, 0.0, EPS), best_t, 1e-5, &dummy_t);

    double3 grad = (double3)(
      (cx_p - cx_m) / (2.0 * EPS),
      (cy_p - cy_m) / (2.0 * EPS),
      (cz_p - cz_m) / (2.0 * EPS)
    );
#endif

    // Project out inward radial component in 3D when clearance <= 0.
    double w_len = length(w);
    if (w_len > 1e-8) {
      double3 u_w = w / w_len;
      double radial = dot(grad, u_w);
      if (best_c <= 0.0 && radial < 0.0) {
        grad -= u_w * radial;
      }
    }

    double g_norm = length(grad);
    if (g_norm < 1e-12) break;
    double3 u_g = grad / g_norm;

    double alpha = step_size;
    bool improved = false;
    for (int ls = 0; ls < 6; ls++) {
      double3 w_cand = w + alpha * u_g;
      double2 cand_t;
      double c_cand = EvalClearanceForW(base_verts, local_edges, local_num_edges,
                                        local_q_outer, w_cand, best_t, 1e-5, &cand_t);
      if (c_cand > best_c) {
        best_c = c_cand;
        best_w = w_cand;
        best_t = cand_t;
        w = w_cand;
        step_size = min(0.01, alpha * 1.3);
        improved = true;
        break;
      }
      alpha *= 0.5;
    }

    if (!improved) {
      step_size *= 0.5;
      if (step_size < 1e-8) break;
    }

    if (best_c > 1e-10 && length(best_w) > 1e-8) {
      if (atomic_cmpxchg((volatile __global int *)&solution->solved, 0, 1) == 0) {
        solution->outer_idx = gid;
        solution->q_outer = local_q_outer;
        solution->w_inner = (double4)(best_w.x, best_w.y, best_w.z, 0.0);
        solution->t_inner = best_t;
        solution->clearance = best_c;
      }
      break;
    }
  }

  int global_idx = get_global_id(0);
  candidates[global_idx].clearance = best_c;
  candidates[global_idx].w_inner = (double4)(best_w.x, best_w.y, best_w.z, 0.0);
  candidates[global_idx].t_inner = best_t;
}
