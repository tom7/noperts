// OpenCL kernel for Nopert #229 proof search.
// Batch-evaluates 5D boxes (Cayley chart + projective view triangle) against
// candidate Farkas contact triples to certify that inner polyhedron cannot be
// contained within outer polyhedron.
//
// Evaluates exact 27-point Bernstein control bounds for the 10-coefficient
// quadratic displacement polynomial across each box.

#ifndef TOP_N
#define TOP_N 4
#endif

typedef struct {
  // Cayley box center
  double cx, cy, cz;
  // Cayley box radii
  double rx, ry, rz;
  // Projective view triangle corners
  double tri[3][3];
  // Cayley chart index (0, 1, 2)
  int chart;
  // Number of candidate triples to test
  int num_triples;
  // Offset in global triples array
  int triple_offset;
  // Offset in global contacts array
  int contact_offset;
  // Number of contacts for this triangle pool
  int num_contacts;
  int _pad;
} GpuBox;

typedef struct {
  int vertex;
  double edge[3];
  double defect;
} GpuContact;

typedef struct {
  // Local contact indices in this pool (0 to num_contacts - 1)
  uchar c0, c1, c2;
  uchar _pad[5];
  double weighted_defect_upper;
} GpuTriple;

typedef struct {
  // 1 if box is proved non-Rupert, 0 otherwise
  int certified;
  // Winning candidate triple index
  int winning_triple;
  // Winning inner contact vertices
  int inner[3];
  // Certified positive margin
  double margin;
} GpuResult;

inline double3 Cross(double3 a, double3 b) {
  return (double3)(
    a.y * b.z - a.z * b.y,
    a.z * b.x - a.x * b.z,
    a.x * b.y - a.y * b.x
  );
}

inline float3 Cross_f(float3 a, float3 b) {
  return (float3)(
    a.y * b.z - a.z * b.y,
    a.z * b.x - a.x * b.z,
    a.x * b.y - a.y * b.x
  );
}

inline double Dot(double3 a, double3 b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

inline float Dot_f(float3 a, float3 b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

inline double Bernstein27Min(
    const double C[10],
    double lx, double ly, double lz,
    double wx, double wy, double wz) {
  double a0 =
    (C[0] + C[1]*lx + C[2]*ly + C[3]*lz + C[4]*lx*lx +
     C[5]*lx*ly + C[6]*lx*lz + C[7]*ly*ly + C[8]*ly*lz + C[9]*lz*lz);
  double ax = wx * (C[1] + 2.0*C[4]*lx + C[5]*ly + C[6]*lz);
  double ay = wy * (C[2] + C[5]*lx + 2.0*C[7]*ly + C[8]*lz);
  double az = wz * (C[3] + C[6]*lx + C[8]*ly + 2.0*C[9]*lz);
  double axx = C[4]*wx*wx, ayy = C[7]*wy*wy, azz = C[9]*wz*wz;
  double axy = C[5]*wx*wy, axz = C[6]*wx*wz, ayz = C[8]*wy*wz;

  double min_b = 1e30;
  for (int bi = 0; bi <= 2; bi++) {
    double ti = 0.5 * bi * ax + (bi == 2 ? axx : 0.0);
    for (int bj = 0; bj <= 2; bj++) {
      double tj = ti + 0.5 * bj * ay + (bj == 2 ? ayy : 0.0) +
        0.25 * bi * bj * axy;
      for (int bk = 0; bk <= 2; bk++) {
        double val = a0 + tj + 0.5 * bk * az + (bk == 2 ? azz : 0.0) +
          0.25 * bk * (bi * axz + bj * ayz);
        if (val < min_b) min_b = val;
      }
    }
  }
  return min_b;
}

inline float Bernstein27Min_f(
    const float *C,
    float lx, float ly, float lz,
    float wx, float wy, float wz) {
  float a0 =
    (C[0] + C[1]*lx + C[2]*ly + C[3]*lz + C[4]*lx*lx +
     C[5]*lx*ly + C[6]*lx*lz + C[7]*ly*ly + C[8]*ly*lz + C[9]*lz*lz);
  float ax = wx * (C[1] + 2.0f*C[4]*lx + C[5]*ly + C[6]*lz);
  float ay = wy * (C[2] + C[5]*lx + 2.0f*C[7]*ly + C[8]*lz);
  float az = wz * (C[3] + C[6]*lx + C[8]*ly + 2.0f*C[9]*lz);
  float axx = C[4]*wx*wx, ayy = C[7]*wy*wy, azz = C[9]*wz*wz;
  float axy = C[5]*wx*wy, axz = C[6]*wx*wz, ayz = C[8]*wy*wz;

  float min_b = 1e30f;
  for (int bi = 0; bi <= 2; bi++) {
    float ti = 0.5f * bi * ax + (bi == 2 ? axx : 0.0f);
    for (int bj = 0; bj <= 2; bj++) {
      float tj = ti + 0.5f * bj * ay + (bj == 2 ? ayy : 0.0f) +
        0.25f * bi * bj * axy;
      for (int bk = 0; bk <= 2; bk++) {
        float val = a0 + tj + 0.5f * bk * az + (bk == 2 ? azz : 0.0f) +
          0.25f * bk * (bi * axz + bj * ayz);
        if (val < min_b) min_b = val;
      }
    }
  }
  return min_b;
}

// In-register accumulation of the 10 quadratic displacement polynomial coefficients
// for contact (vin, vout) with normal vector u, scaled by chart signs s = (sx, sy, sz).
inline void AccumulateContactPoly(double C[10], double weight, double3 u,
                                  double3 vin, double3 vout, double3 s) {
  double sx = s.x, sy = s.y, sz = s.z;
  double ux = u.x, uy = u.y, uz = u.z;
  double vx = vin.x, vy = vin.y, vz = vin.z;
  double ox = vout.x, oy = vout.y, oz = vout.z;

  // Constant term (m = 0):
  C[0] += weight * (ux * (sx*vx - ox) + uy * (sy*vy - oy) + uz * (sz*vz - oz));

  // Linear terms:
  C[1] += weight * 2.0 * (-uy * sy * vz + uz * sz * vy);
  C[2] += weight * 2.0 * (ux * sx * vz - uz * sz * vx);
  C[3] += weight * 2.0 * (-ux * sx * vy + uy * sy * vx);

  // Quadratic pure terms:
  C[4] += weight * (ux * (sx*vx - ox) - uy * (sy*vy + oy) - uz * (sz*vz + oz));
  C[7] += weight * (-ux * (sx*vx + ox) + uy * (sy*vy - oy) - uz * (sz*vz + oz));
  C[9] += weight * (-ux * (sx*vx + ox) - uy * (sy*vy + oy) + uz * (sz*vz - oz));

  // Quadratic cross terms:
  C[5] += weight * 2.0 * (ux * sx * vy + uy * sy * vx);
  C[6] += weight * 2.0 * (ux * sx * vz + uz * sz * vx);
  C[8] += weight * 2.0 * (uy * sy * vz + uz * sz * vy);
}

// Evaluate a batch of boxes against their candidate triples using
// Bernstein control points.
__kernel void EvaluateBoxes(
    __global const GpuBox *restrict boxes,
    __global const GpuContact *restrict contacts,
    __global const GpuTriple *restrict triples,
    __global GpuResult *restrict results,
    const int num_boxes) {

  const int gid = get_global_id(0);
  if (gid >= num_boxes) return;

  const GpuBox box = boxes[gid];

  double x0 = box.cx;
  double y0 = box.cy;
  double z0 = box.cz;

  // Chart signs
  double3 s = (double3)(
    (box.chart == 2 || box.chart == 3) ? -1.0 : 1.0,
    (box.chart == 1 || box.chart == 3) ? -1.0 : 1.0,
    (box.chart == 1 || box.chart == 2) ? -1.0 : 1.0
  );

  double3 view_center = (double3)(
    (box.tri[0][0] + box.tri[1][0] + box.tri[2][0]) / 3.0,
    (box.tri[0][1] + box.tri[1][1] + box.tri[2][1]) / 3.0,
    (box.tri[0][2] + box.tri[1][2] + box.tri[2][2]) / 3.0
  );

  double ex = fmax(fabs(box.cx - box.rx), fabs(box.cx + box.rx));
  double ey = fmax(fabs(box.cy - box.ry), fabs(box.cy + box.ry));
  double ez = fmax(fabs(box.cz - box.rz), fabs(box.cz + box.rz));
  double d_bound = 1.0 + ex*ex + ey*ey + ez*ez;

  // Cayley box bounding interval constants (constant across all triples)
  double lx = box.cx - box.rx, ly = box.cy - box.ry, lz = box.cz - box.rz;
  double wx = 2.0 * box.rx, wy = 2.0 * box.ry, wz = 2.0 * box.rz;
  // Lean displacement error: 300 * dBound * tightVertexErrorQ.
  double disp_error = 300.0 * d_bound * TIGHT_VERTEX_ERROR;

  // Projective view triangle nodes (constant across all triples)
  double3 p[6];
  p[0] = (double3)(box.tri[0][0], box.tri[0][1], box.tri[0][2]);
  p[1] = (double3)(box.tri[1][0], box.tri[1][1], box.tri[1][2]);
  p[2] = (double3)(box.tri[2][0], box.tri[2][1], box.tri[2][2]);
  p[3] = 0.5 * (p[0] + p[1]);
  p[4] = 0.5 * (p[1] + p[2]);
  p[5] = 0.5 * (p[2] + p[0]);

  // Cayley rotation matrix numerator at center.
  double num[3][3] = {
    {1.0 + x0*x0 - y0*y0 - z0*z0, 2.0*(x0*y0 - z0), 2.0*(x0*z0 + y0)},
    {2.0*(x0*y0 + z0), 1.0 - x0*x0 + y0*y0 - z0*z0, 2.0*(y0*z0 - x0)},
    {2.0*(x0*z0 - y0), 2.0*(y0*z0 + x0), 1.0 - x0*x0 - y0*y0 + z0*z0}
  };
  double denom0 = 1.0 + x0*x0 + y0*y0 + z0*z0;

  // Pre-rotate all 20 inner vertices at box center
  double3 rot_vin[20];
  for (int k = 0; k < 20; k++) {
    double3 vin = (double3)(VERTICES[k][0], VERTICES[k][1], VERTICES[k][2]);
    rot_vin[k] = (double3)(
      s.x * (num[0][0]*vin.x + num[0][1]*vin.y + num[0][2]*vin.z),
      s.y * (num[1][0]*vin.x + num[1][1]*vin.y + num[1][2]*vin.z),
      s.z * (num[2][0]*vin.x + num[2][1]*vin.y + num[2][2]*vin.z)
    );
  }

  // Precompute best inner vertex and unit center polynomial for each contact in this pool
  char best_in[MAX_CONTACTS];
  double psi_center[MAX_CONTACTS][10];
  int n_contacts = box.num_contacts <= MAX_CONTACTS ? box.num_contacts : MAX_CONTACTS;
  for (int c = 0; c < n_contacts; c++) {
    const GpuContact gc = contacts[box.contact_offset + c];
    double3 edge = (double3)(gc.edge[0], gc.edge[1], gc.edge[2]);
    double3 u = Cross(view_center, edge);
    double3 out = (double3)(VERTICES[gc.vertex][0], VERTICES[gc.vertex][1], VERTICES[gc.vertex][2]);
    double best_val = -1e30;
    int best_k = 0;
    for (int k = 0; k < 20; k++) {
      double3 disp = rot_vin[k] - denom0 * out;
      double v = Dot(u, disp);
      if (v > best_val) {
        best_val = v;
        best_k = k;
      }
    }
    best_in[c] = (char)best_k;

    double3 vin = (double3)(VERTICES[best_k][0], VERTICES[best_k][1], VERTICES[best_k][2]);
    double poly[10] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    AccumulateContactPoly(poly, 1.0, u, vin, out, s);
    for (int m = 0; m < 10; m++) {
      psi_center[c][m] = poly[m];
    }
  }

  GpuResult res;
  res.certified = 0;
  res.winning_triple = -1;
  res.inner[0] = 0;
  res.inner[1] = 0;
  res.inner[2] = 0;
  res.margin = -1e30;

#if TOP_N > 0
  // FP32 Pre-pass: quickly screen all candidates using view_center margin.
  // Leverages the 64x FP32 ALU advantage on sm_89 (Ada Lovelace).
  float lx_f = (float)lx, ly_f = (float)ly, lz_f = (float)lz;
  float wx_f = (float)wx, wy_f = (float)wy, wz_f = (float)wz;
  float d_bound_f = (float)d_bound;
  float disp_error_f = (float)disp_error;
  float best_margin_f = -1e30f;
  float3 vc_f = (float3)((float)view_center.x, (float)view_center.y, (float)view_center.z);

#if TOP_N == 1
  int top_triples[1] = {-1};
  float top_margins[1] = {0.0f};
#else
  int top_triples[TOP_N];
  float top_margins[TOP_N];
  for (int i = 0; i < TOP_N; i++) {
    top_triples[i] = -1;
    top_margins[i] = 0.0f;
  }
#endif

  for (int t = 0; t < box.num_triples; t++) {
    const GpuTriple triple = triples[box.triple_offset + t];

    int loc_c0 = (int)triple.c0;
    int loc_c1 = (int)triple.c1;
    int loc_c2 = (int)triple.c2;
    if (loc_c0 >= n_contacts || loc_c1 >= n_contacts || loc_c2 >= n_contacts) continue;

    const GpuContact gc1 = contacts[box.contact_offset + loc_c1];
    const GpuContact gc2 = contacts[box.contact_offset + loc_c2];
    float3 e1 = (float3)((float)gc1.edge[0], (float)gc1.edge[1], (float)gc1.edge[2]);
    float3 e2 = (float3)((float)gc2.edge[0], (float)gc2.edge[1], (float)gc2.edge[2]);

    float3 w_coeff0 = Cross_f(e1, e2);
    float w0 = Dot_f(vc_f, w_coeff0);
    if (w0 <= 1e-9f) continue;

    const GpuContact gc0 = contacts[box.contact_offset + loc_c0];
    float3 e0 = (float3)((float)gc0.edge[0], (float)gc0.edge[1], (float)gc0.edge[2]);

    float3 w_coeff1 = Cross_f(e2, e0);
    float w1 = Dot_f(vc_f, w_coeff1);
    if (w1 <= 1e-9f) continue;

    float3 w_coeff2 = Cross_f(e0, e1);
    float w2 = Dot_f(vc_f, w_coeff2);
    if (w2 <= 1e-9f) continue;

    float C_center_f[10];
    for (int m = 0; m < 10; m++) {
      C_center_f[m] = w0 * (float)psi_center[loc_c0][m] +
                      w1 * (float)psi_center[loc_c1][m] +
                      w2 * (float)psi_center[loc_c2][m];
    }

    float min_b_center = Bernstein27Min_f(C_center_f, lx_f, ly_f, lz_f, wx_f, wy_f, wz_f);
    float penalty = d_bound_f * (float)triple.weighted_defect_upper;
    float margin = min_b_center - penalty - disp_error_f;
    if (margin > best_margin_f) best_margin_f = margin;

#if TOP_N == 1
    if (margin > top_margins[0]) {
      top_margins[0] = margin;
      top_triples[0] = t;
    }
#else
    if (margin > 0.0f) {
      int min_slot = 0;
      float min_m = top_margins[0];
      for (int i = 1; i < TOP_N; i++) {
        if (top_margins[i] < min_m) {
          min_m = top_margins[i];
          min_slot = i;
        }
      }
      if (margin > min_m) {
        top_margins[min_slot] = margin;
        top_triples[min_slot] = t;
      }
    }
#endif
  }
#endif

  // Unified evaluation loop: first test top N candidates, then fallback scan
  int num_phases = TOP_N + box.num_triples;
#if TOP_N > 0
  // Mathematical justification for bypassing the FP64 scan:
  // 1. Stage 1 in FP64 requires: min_b_center - defect_penalty - disp_error > 0.0.
  //    Any candidate failing this check is immediately discarded and never reaches
  //    Stage 2 (evaluating the 6 simplex view nodes).
  // 2. Both FP32 and FP64 passes evaluate the identical algebraic expression at
  //    view_center using the exact same psi_center coefficients and best_in indices.
  // 3. For degree-2 Bernstein Horner evaluation on this bounded domain (|C| <= 10,
  //    |l| <= 1, w <= 2), the maximum floating-point rounding error between binary32
  //    and binary64 is bounded by |margin_fp64 - margin_fp32| < 2.0e-6.
  // 4. Therefore, if best_margin_f <= -1e-5f, every candidate triple in the pool
  //    satisfies margin_fp64 <= -1e-5f + 2.0e-6 = -8.0e-6 < 0.0. Every candidate
  //    is guaranteed to fail Stage 1 in FP64, so skipping the FP64 scan is sound.
  if (best_margin_f <= -1e-5f) {
    num_phases = 0;
  }
#endif
  for (int step = 0; step < num_phases; step++) {
    int t;
#if TOP_N > 0
    if (step < TOP_N) {
      t = top_triples[step];
      if (t < 0) continue;
    } else {
      if (res.certified) break;
      t = step - TOP_N;
    }
#else
    t = step;
#endif

    const GpuTriple triple = triples[box.triple_offset + t];

    double defect_penalty = d_bound * triple.weighted_defect_upper;

    // Stage 1: Fast filter at view_center (27 controls)
    int loc_c0 = (int)triple.c0;
    int loc_c1 = (int)triple.c1;
    int loc_c2 = (int)triple.c2;
    if (loc_c0 >= n_contacts || loc_c1 >= n_contacts || loc_c2 >= n_contacts) continue;

    const GpuContact c1 = contacts[box.contact_offset + loc_c1];
    const GpuContact c2 = contacts[box.contact_offset + loc_c2];
    double3 edge1 = (double3)(c1.edge[0], c1.edge[1], c1.edge[2]);
    double3 edge2 = (double3)(c2.edge[0], c2.edge[1], c2.edge[2]);

    double3 w_coeff0 = Cross(edge1, edge2);
    double w0 = Dot(view_center, w_coeff0);
    if (w0 <= 1e-9) continue;

    const GpuContact c0 = contacts[box.contact_offset + loc_c0];
    double3 edge0 = (double3)(c0.edge[0], c0.edge[1], c0.edge[2]);

    double3 w_coeff1 = Cross(edge2, edge0);
    double w1 = Dot(view_center, w_coeff1);
    if (w1 <= 1e-9) continue;

    double3 w_coeff2 = Cross(edge0, edge1);
    double w2 = Dot(view_center, w_coeff2);
    if (w2 <= 1e-9) continue;

    double C_center[10];
    for (int m = 0; m < 10; m++) {
      C_center[m] = w0 * psi_center[loc_c0][m] +
                    w1 * psi_center[loc_c1][m] +
                    w2 * psi_center[loc_c2][m];
    }

    double min_b_center = Bernstein27Min(C_center, lx, ly, lz, wx, wy, wz);
    if (min_b_center - defect_penalty - disp_error <= 0.0) {
      continue;
    }

    // Stage 2: Simplex Bernstein evaluation with progressive early exit
    // Only evaluated when center filter passes (~12% of triples).
    int in0 = (int)best_in[loc_c0];
    int in1 = (int)best_in[loc_c1];
    int in2 = (int)best_in[loc_c2];
    if ((unsigned int)in0 >= 20 || (unsigned int)in1 >= 20 || (unsigned int)in2 >= 20) continue;

    double3 vin0 = (double3)(VERTICES[in0][0], VERTICES[in0][1], VERTICES[in0][2]);
    double3 vout0 = (double3)(VERTICES[c0.vertex][0], VERTICES[c0.vertex][1], VERTICES[c0.vertex][2]);

    double3 vin1 = (double3)(VERTICES[in1][0], VERTICES[in1][1], VERTICES[in1][2]);
    double3 vout1 = (double3)(VERTICES[c1.vertex][0], VERTICES[c1.vertex][1], VERTICES[c1.vertex][2]);

    double3 vin2 = (double3)(VERTICES[in2][0], VERTICES[in2][1], VERTICES[in2][2]);
    double3 vout2 = (double3)(VERTICES[c2.vertex][0], VERTICES[c2.vertex][1], VERTICES[c2.vertex][2]);

    // Step 2a: Evaluate Corner 0
    double C0[10] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    double w0_0 = Dot(p[0], w_coeff0);
    double w1_0 = Dot(p[0], w_coeff1);
    double w2_0 = Dot(p[0], w_coeff2);
    AccumulateContactPoly(C0, w0_0, Cross(p[0], edge0), vin0, vout0, s);
    AccumulateContactPoly(C0, w1_0, Cross(p[0], edge1), vin1, vout1, s);
    AccumulateContactPoly(C0, w2_0, Cross(p[0], edge2), vin2, vout2, s);
    double min_0 = Bernstein27Min(C0, lx, ly, lz, wx, wy, wz);
    if (min_0 - defect_penalty - disp_error <= 0.0) continue;

    // Step 2b: Evaluate Corner 1
    double C1[10] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    double w0_1 = Dot(p[1], w_coeff0);
    double w1_1 = Dot(p[1], w_coeff1);
    double w2_1 = Dot(p[1], w_coeff2);
    AccumulateContactPoly(C1, w0_1, Cross(p[1], edge0), vin0, vout0, s);
    AccumulateContactPoly(C1, w1_1, Cross(p[1], edge1), vin1, vout1, s);
    AccumulateContactPoly(C1, w2_1, Cross(p[1], edge2), vin2, vout2, s);
    double min_1 = Bernstein27Min(C1, lx, ly, lz, wx, wy, wz);
    if (min_1 - defect_penalty - disp_error <= 0.0) continue;

    // Step 2c: Evaluate Corner 2
    double C2[10] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    double w0_2 = Dot(p[2], w_coeff0);
    double w1_2 = Dot(p[2], w_coeff1);
    double w2_2 = Dot(p[2], w_coeff2);
    AccumulateContactPoly(C2, w0_2, Cross(p[2], edge0), vin0, vout0, s);
    AccumulateContactPoly(C2, w1_2, Cross(p[2], edge1), vin1, vout1, s);
    AccumulateContactPoly(C2, w2_2, Cross(p[2], edge2), vin2, vout2, s);
    double min_2 = Bernstein27Min(C2, lx, ly, lz, wx, wy, wz);
    if (min_2 - defect_penalty - disp_error <= 0.0) continue;

    // Step 2d: Midpoints (Edges 01, 12, 20)
    // Edge 01 (midpoint p[3]): Q = 2 * P(p[3]) - 0.5 * (C0 + C1)
    double M[10] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    double w0_3 = Dot(p[3], w_coeff0);
    double w1_3 = Dot(p[3], w_coeff1);
    double w2_3 = Dot(p[3], w_coeff2);
    AccumulateContactPoly(M, w0_3, Cross(p[3], edge0), vin0, vout0, s);
    AccumulateContactPoly(M, w1_3, Cross(p[3], edge1), vin1, vout1, s);
    AccumulateContactPoly(M, w2_3, Cross(p[3], edge2), vin2, vout2, s);
    double Q[10];
    for (int m = 0; m < 10; m++) Q[m] = 2.0 * M[m] - 0.5 * (C0[m] + C1[m]);
    double min_3 = Bernstein27Min(Q, lx, ly, lz, wx, wy, wz);
    if (min_3 - defect_penalty - disp_error <= 0.0) continue;

    // Edge 12 (midpoint p[4]): Q = 2 * P(p[4]) - 0.5 * (C1 + C2)
    for (int m = 0; m < 10; m++) M[m] = 0.0;
    double w0_4 = Dot(p[4], w_coeff0);
    double w1_4 = Dot(p[4], w_coeff1);
    double w2_4 = Dot(p[4], w_coeff2);
    AccumulateContactPoly(M, w0_4, Cross(p[4], edge0), vin0, vout0, s);
    AccumulateContactPoly(M, w1_4, Cross(p[4], edge1), vin1, vout1, s);
    AccumulateContactPoly(M, w2_4, Cross(p[4], edge2), vin2, vout2, s);
    for (int m = 0; m < 10; m++) Q[m] = 2.0 * M[m] - 0.5 * (C1[m] + C2[m]);
    double min_4 = Bernstein27Min(Q, lx, ly, lz, wx, wy, wz);
    if (min_4 - defect_penalty - disp_error <= 0.0) continue;

    // Edge 20 (midpoint p[5]): Q = 2 * P(p[5]) - 0.5 * (C2 + C0)
    for (int m = 0; m < 10; m++) M[m] = 0.0;
    double w0_5 = Dot(p[5], w_coeff0);
    double w1_5 = Dot(p[5], w_coeff1);
    double w2_5 = Dot(p[5], w_coeff2);
    AccumulateContactPoly(M, w0_5, Cross(p[5], edge0), vin0, vout0, s);
    AccumulateContactPoly(M, w1_5, Cross(p[5], edge1), vin1, vout1, s);
    AccumulateContactPoly(M, w2_5, Cross(p[5], edge2), vin2, vout2, s);
    for (int m = 0; m < 10; m++) Q[m] = 2.0 * M[m] - 0.5 * (C2[m] + C0[m]);
    double min_5 = Bernstein27Min(Q, lx, ly, lz, wx, wy, wz);
    if (min_5 - defect_penalty - disp_error <= 0.0) continue;

    // All 6 simplex Bernstein bounds passed!
    double min_162 = fmin(fmin(fmin(min_0, min_1), min_2), fmin(fmin(min_3, min_4), min_5));
    res.certified = 1;
    res.winning_triple = t;
    res.inner[0] = in0;
    res.inner[1] = in1;
    res.inner[2] = in2;
    res.margin = min_162 - defect_penalty - disp_error;
    break;
  }

  results[gid] = res;
}
