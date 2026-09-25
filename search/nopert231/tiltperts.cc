#include <CL/cl.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <format>
#include <fstream>
#include <sstream>
#include <numbers>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "ansi.h"
#include "arcfour.h"
#include "base/logging.h"
#include "base/print.h"
#include "geom/hull-2d.h"
#include "geom/polyhedra.h"
#include "opencl/clutil.h"
#include "periodically.h"
#include "randutil.h"
#include "ruperts-util.h"
#include "solutions.h"
#include "status-bar.h"
#include "timer.h"
#include "util.h"
#include "yocto-math.h"

static CL *cl = nullptr;

static constexpr int MAX_EDGES = 32;

struct alignas(32) GpuEdge {
  vec2 normal;
  double b;
  double _pad;
};

struct alignas(32) GpuOuterPose {
  quat4 q_outer;
  int num_edges;
  int _pad[7];
  GpuEdge edges[MAX_EDGES];
};

struct SeedPoint {

  quat4 q_outer = {0, 0, 0, 1};
  vec3 w_inner = {0, 0, 0};
  vec2 t_inner = {0, 0};
  bool has_w = false;
  bool has_t = false;
};

static std::vector<SeedPoint> LoadSeedPoints(const std::string &filename) {
  std::vector<SeedPoint> seeds;
  std::ifstream f(filename);
  if (!f.is_open()) {
    Print(ARED("Failed to open seed file: {}\n"), filename);
    return seeds;
  }
  std::string line;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    std::vector<double> vals;
    double v;
    while (iss >> v) {
      vals.push_back(v);
    }
    if (vals.size() < 4) continue;
    SeedPoint sp;
    sp.q_outer = quat4{vals[0], vals[1], vals[2], vals[3]};
    if (vals.size() >= 7) {
      sp.w_inner = vec3{vals[4], vals[5], vals[6]};
      sp.has_w = true;
    }
    if (vals.size() >= 9) {
      sp.t_inner = vec2{vals[7], vals[8]};
      sp.has_t = true;
    }
    seeds.push_back(sp);
  }
  Print("Loaded " ACYAN("{}") " seed points from {}\n", seeds.size(), filename);
  return seeds;
}


struct alignas(32) GpuSolution {
  int solved;
  int outer_idx;
  int _pad[6];
  quat4 q_outer;
  quat4 w_inner;
  vec2 t_inner;
  double clearance;
  double _pad2;
};

struct alignas(32) GpuCandidate {
  double clearance;
  double _pad;
  vec2 t_inner;
  quat4 w_inner;
};

static_assert(sizeof(GpuEdge) == 32);
static_assert(sizeof(GpuOuterPose) == 1088);
static_assert(sizeof(GpuSolution) == 128);
static_assert(sizeof(GpuCandidate) == 64);



static inline quat4 RotationVectorToQuat(const vec3 &w) {
  const double theta = yocto::length(w);
  if (theta < 1e-12) {
    return quat4{0.0, 0.0, 0.0, 1.0};
  }
  return QuatFromVec(yocto::rotation_quat(w / theta, theta));
}

static vec3 FaceNormal(const std::vector<vec3> &vertices,
                       const std::vector<int> &face) {
  CHECK(face.size() >= 3);
  const vec3 &v0 = vertices[face[0]];
  const vec3 &v1 = vertices[face[1]];
  const vec3 &v2 = vertices[face[2]];
  return yocto::normalize(yocto::cross(v1 - v0, v2 - v0));
}

static quat4 MakeTwoFacesParallelToZ(const std::vector<vec3> &vertices,
                                     const std::vector<int> &face1,
                                     const std::vector<int> &face2) {
  if (face1.size() < 3 || face2.size() < 3)
    return quat4{0.0, 0.0, 0.0, 1.0};

  const vec3 face1_normal = FaceNormal(vertices, face1);
  const vec3 face2_normal = FaceNormal(vertices, face2);

  vec3 x_axis = vec3{1.0, 0.0, 0.0};
  vec3 rot_axis = yocto::cross(face1_normal, x_axis);
  double rot1_angle = yocto::angle(face1_normal, x_axis);

  quat4 rot1 = QuatFromVec(yocto::rotation_quat(rot_axis, rot1_angle));

  const vec3 rot_face2_normal =
    yocto::transform_direction(yocto::rotation_frame(rot1), face2_normal);

  vec3 proj_normal = vec3{0.0, rot_face2_normal.y, rot_face2_normal.z};
  double rot2_angle = yocto::angle(proj_normal, vec3{0.0, 1.0, 0.0});
  quat4 rot2 = QuatFromVec(yocto::rotation_quat({1.0, 0.0, 0.0}, rot2_angle));

  return normalize(rot2 * rot1);
}

static quat4 AlignFaces(const std::vector<vec3> &vertices,
                        const std::vector<int> &face1,
                        const std::vector<int> &face2) {
  const quat4 parallel_inner_rot = MakeTwoFacesParallelToZ(
      vertices, face1, face2);
  const vec3 face1_normal = FaceNormal(vertices, face1);
  const vec3 xy_normal = yocto::transform_direction(
      yocto::rotation_frame(parallel_inner_rot), face1_normal);

  CHECK(std::abs(xy_normal.z) < 0.01) << "The rotated face 1 normal "
    "should already be in the x/y plane: " << VecString(xy_normal);

  const double rot3_angle = std::atan2(xy_normal.x, xy_normal.y) +
    std::numbers::pi * 0.5;
  const quat4 rot3 =
    QuatFromVec(yocto::rotation_quat({0.0, 0.0, 1.0}, rot3_angle));

  return normalize(rot3 * parallel_inner_rot);
}

static void ProjectVertices(const frame3 &f,
                            const std::vector<vec3> &vertices,
                            std::vector<vec2> &pts) {
  for (size_t i = 0; i < vertices.size(); i++) {
    const vec3 &v = vertices[i];
    pts[i] = vec2{
        f.x.x * v.x + f.y.x * v.y + f.z.x * v.z + f.o.x,
        f.x.y * v.x + f.y.y * v.y + f.z.y * v.z + f.o.y,
    };
  }
}

struct TiltGPU {
  TiltGPU(SolutionDB *db,
          const Polyhedron &poly,
          int batch_size = 512,
          int threads_per_pose = 128,
          int max_steps = 25,
          bool dump_ptx = false,
          bool forward_diff = true,
          const std::vector<SeedPoint> &seed_points = {},
          double seed_sigma = 0.001)
      : rc(std::format("tiltgpu.{}", time(nullptr))),
        db(db),
        poly(poly),
        num_vertices(poly.vertices.size()),
        batch_size(batch_size),
        threads_per_pose(threads_per_pose),
        max_steps(max_steps),
        forward_diff(forward_diff),
        seed_points(seed_points),
        seed_sigma(seed_sigma),
        status(STATUS_LINES) {


    CHECK(batch_size > 0);
    CHECK(threads_per_pose > 0);

    std::string defines =
        std::format("#define NUM_VERTICES {}\n", num_vertices);
    if (forward_diff) {
      defines += "#define FORWARD_DIFFERENCE 1\n";
    }

    std::string kernel_src = defines + Util::ReadFile("tiltperts.cl");
    const auto &[prg, kernels] =
        cl->BuildKernels(kernel_src, {"TiltGradAscent"}, 1);
    program = prg;

    if (dump_ptx) {
      if (const auto ptx = CL::DecodeProgram(program)) {
        Util::WriteFile("tiltperts_nvidia.ptx", *ptx);
        Print(AGREEN("Dumped driver PTX to tiltperts_nvidia.ptx ({} bytes).\n"), ptx->size());
      } else {
        Print(ARED("CL::DecodeProgram did not return text (e.g. driver is PoCL on CPU).\n"));
      }
    }

    auto it = kernels.find("TiltGradAscent");
    CHECK(it != kernels.end());
    tilt_kernel = it->second;

    // Flatten vertices
    std::vector<double> flat_verts;
    flat_verts.reserve(num_vertices * 3);
    for (const vec3 &v : poly.vertices) {
      flat_verts.push_back(v.x);
      flat_verts.push_back(v.y);
      flat_verts.push_back(v.z);
    }
    base_verts_buf = CopyMemoryToGPU<double>(cl->context, cl->queue,
                                             flat_verts, /*readonly=*/true);

    outer_poses_buf = CreateUninitializedGPUMemory<GpuOuterPose>(
        cl->context, batch_size);
    solution_buf =
        CreateUninitializedGPUMemory<GpuSolution>(cl->context, 1);
    candidates_buf = CreateUninitializedGPUMemory<GpuCandidate>(
        cl->context, batch_size * threads_per_pose);

    host_outer_poses.resize(batch_size);
  }

  ~TiltGPU() {
    CHECK_SUCCESS(clReleaseKernel(tilt_kernel));
    CHECK_SUCCESS(clReleaseProgram(program));
    CHECK_SUCCESS(clReleaseMemObject(base_verts_buf));
    CHECK_SUCCESS(clReleaseMemObject(outer_poses_buf));
    CHECK_SUCCESS(clReleaseMemObject(solution_buf));
    CHECK_SUCCESS(clReleaseMemObject(candidates_buf));
  }

  bool RefineCandidateCPU(const GpuOuterPose &pose,
                          const GpuCandidate &cand,
                          frame3 *out_outer,
                          frame3 *out_inner) {
    const quat4 q_outer = pose.q_outer;
    vec3 w = vec3{cand.w_inner.x, cand.w_inner.y, cand.w_inner.z};
    vec2 best_trans = cand.t_inner;
    double best_clearance = cand.clearance;

    std::vector<vec2> outer_verts(num_vertices);
    std::vector<vec2> inner_verts(num_vertices);

    vec3 phi = vec3{0.0, 0.0, 0.0};
    double outer_step = 2e-4;

    auto EvalOuterInner = [&](const vec3 &p_outer, const vec3 &w_inner,
                              vec2 t_hint,
                              double initial_step = 1e-5) -> Clearance2D {
      const quat4 d_qo = RotationVectorToQuat(p_outer);
      const quat4 qo = yocto::normalize(d_qo * q_outer);
      const frame3 fo = yocto::rotation_frame(qo);
      ProjectVertices(fo, poly.vertices, outer_verts);
      const std::vector<int> ho = Hull2D::QuickHull(outer_verts);
      if (ho.size() < 3)
        return Clearance2D{.clearance = -1.0, .translation = vec2{0.0, 0.0}};
      const auto eo = GetHullEdges(outer_verts, ho);

      const quat4 d_qi = RotationVectorToQuat(w_inner);
      const quat4 qi = yocto::normalize(d_qi * qo);
      const frame3 fi = yocto::rotation_frame(qi);
      ProjectVertices(fi, poly.vertices, inner_verts);

      return MaximizeClearance2D(eo, inner_verts, t_hint, initial_step);
    };

    for (int iter = 0; iter < 15; iter++) {
      if (best_clearance > 1e-9) break;

      constexpr double EPS = 1e-5;
      const double c_xp = EvalOuterInner(phi + vec3{EPS, 0, 0}, w, best_trans).clearance;
      const double c_xm = EvalOuterInner(phi - vec3{EPS, 0, 0}, w, best_trans).clearance;
      const double c_yp = EvalOuterInner(phi + vec3{0, EPS, 0}, w, best_trans).clearance;
      const double c_ym = EvalOuterInner(phi - vec3{0, EPS, 0}, w, best_trans).clearance;
      const double c_zp = EvalOuterInner(phi + vec3{0, 0, EPS}, w, best_trans).clearance;
      const double c_zm = EvalOuterInner(phi - vec3{0, 0, EPS}, w, best_trans).clearance;

      const vec3 g_phi = vec3{
          (c_xp - c_xm) / (2.0 * EPS),
          (c_yp - c_ym) / (2.0 * EPS),
          (c_zp - c_zm) / (2.0 * EPS),
      };
      const double g_len = yocto::length(g_phi);
      if (g_len < 1e-12) break;
      const vec3 u_phi = g_phi / g_len;

      double alpha = outer_step;
      bool improved = false;
      for (int ls = 0; ls < 6; ls++) {
        const vec3 phi_cand = phi + u_phi * alpha;
        const auto res = EvalOuterInner(phi_cand, w, best_trans, 1e-5);
        if (res.clearance > best_clearance) {
          best_clearance = res.clearance;
          phi = phi_cand;
          best_trans = res.translation;
          outer_step = std::min(0.005, alpha * 1.3);
          improved = true;
          break;
        }
        alpha *= 0.5;
      }
      if (!improved) {
        outer_step *= 0.5;
        if (outer_step < 1e-8) break;
      }
    }

    if (best_clearance > 1e-9) {
      const quat4 d_qo = RotationVectorToQuat(phi);
      const quat4 final_qo = yocto::normalize(d_qo * q_outer);
      const frame3 fo = yocto::rotation_frame(final_qo);

      const quat4 d_qi = RotationVectorToQuat(w);
      const quat4 final_qi = yocto::normalize(d_qi * final_qo);
      const frame3 fi = yocto::translation_frame(vec3{best_trans.x, best_trans.y, 0.0}) *
                        yocto::rotation_frame(final_qi);

      const auto cl = GetClearance(poly, fo, fi);
      if (cl.has_value() && cl.value() > 0.0) {
        *out_outer = fo;
        *out_inner = fi;
        return true;
      }
    }
    return false;
  }

  void Run(int max_batches = -1) {
    Timer run_timer;
    Periodically status_per(0.5);
    Periodically flush_per(20.0 * 60.0);

    int64_t total_outer_poses = 0;
    int64_t total_trajectories = 0;
    double highest_clearance_seen = -1.0;
    int batch_num = 0;

    int64_t unflushed_outer_poses = 0;
    int64_t unflushed_trajectories = 0;
    std::optional<double> unflushed_highest_clearance;

    auto FlushAttempts = [&]() {
        if (unflushed_outer_poses > 0 && unflushed_highest_clearance.has_value()) {
          db->AddAttempt(poly.name, SolutionDB::METHOD_TILT_GPU, 0,
                         -unflushed_highest_clearance.value(),
                         unflushed_outer_poses, unflushed_trajectories);
          unflushed_outer_poses = 0;
          unflushed_trajectories = 0;
          unflushed_highest_clearance = std::nullopt;
        }
      };

    std::vector<vec2> outer_pts(num_vertices);

    for (;;) {
      if (max_batches > 0 && batch_num >= max_batches) break;
      batch_num++;

      // Generate outer poses on CPU.
      for (int i = 0; i < batch_size; i++) {
        quat4 q_outer;
        for (;;) {
          if (!seed_points.empty()) {
            const SeedPoint &sp = seed_points[RandTo(&rc, seed_points.size())];
            if (seed_sigma > 0.0 && RandDouble(&rc) >= 0.20) {
              auto RandNorm = [&]() {
                double u1 = std::max(1e-15, RandDouble(&rc));
                double u2 = RandDouble(&rc);
                return std::sqrt(-2.0 * std::log(u1)) * std::cos(2.0 * std::numbers::pi * u2);
              };
              vec3 delta = {RandNorm() * seed_sigma, RandNorm() * seed_sigma, RandNorm() * seed_sigma};
              quat4 d_q = RotationVectorToQuat(delta);
              q_outer = yocto::normalize(d_q * sp.q_outer);
            } else {
              q_outer = sp.q_outer;
            }
          } else {
            const int mode = RandTo(&rc, 10);
            if (mode < 4 && poly.faces != nullptr &&
                poly.faces->v.size() >= 2) {
              const auto &[f1, f2] = TwoNonParallelFaces(&rc, poly);
              q_outer = AlignFaces(poly.vertices, poly.faces->v[f1], poly.faces->v[f2]);
            } else {
              q_outer = RandomQuaternion(&rc);
            }
          }

          const frame3 outer_frame = yocto::rotation_frame(q_outer);
          ProjectVertices(outer_frame, poly.vertices, outer_pts);

          const std::vector<int> hull_idx = Hull2D::QuickHull(outer_pts);
          if (hull_idx.size() < 3 || hull_idx.size() > MAX_EDGES) continue;

          const std::vector<PolygonEdge> edges = GetHullEdges(outer_pts, hull_idx);
          if (edges.empty()) continue;

          host_outer_poses[i].q_outer = q_outer;
          host_outer_poses[i].num_edges = edges.size();
          for (size_t e = 0; e < edges.size(); e++) {
            host_outer_poses[i].edges[e].normal = edges[e].normal;
            host_outer_poses[i].edges[e].b = edges[e].b;
            host_outer_poses[i].edges[e]._pad = 0.0;
          }
          break;
        }
      }



      // Initialize the Kernel args.
      CopyBufferToGPU<GpuOuterPose>(cl->queue, host_outer_poses, outer_poses_buf);

      // Reset solution buffer.
      GpuSolution init_sol = {};
      init_sol.solved = 0;
      CopyBufferToGPU<GpuSolution>(cl->queue, {init_sol}, solution_buf);

      CHECK_SUCCESS(clSetKernelArg(tilt_kernel, 0, sizeof(cl_mem), (void *)&base_verts_buf));
      CHECK_SUCCESS(clSetKernelArg(tilt_kernel, 1, sizeof(cl_mem), (void *)&outer_poses_buf));
      CHECK_SUCCESS(clSetKernelArg(tilt_kernel, 2, sizeof(int), (void *)&max_steps));
      CHECK_SUCCESS(clSetKernelArg(tilt_kernel, 3, sizeof(cl_mem), (void *)&solution_buf));
      CHECK_SUCCESS(clSetKernelArg(tilt_kernel, 4, sizeof(cl_mem), (void *)&candidates_buf));

      const size_t global_work_size[1] = { (size_t)(batch_size * threads_per_pose) };
      const size_t local_work_size[1] = { (size_t)threads_per_pose };

      // Run it.
      CHECK_SUCCESS(clEnqueueNDRangeKernel(
          cl->queue, tilt_kernel, 1, nullptr,
          global_work_size, local_work_size, 0, nullptr, nullptr));
      CHECK_SUCCESS(clFinish(cl->queue));

      total_outer_poses += batch_size;
      total_trajectories += batch_size * threads_per_pose;
      unflushed_outer_poses += batch_size;
      unflushed_trajectories += batch_size * threads_per_pose;

      // Did we find any solution?
      const auto sol_vec = CopyBufferFromGPU<GpuSolution>(cl->queue, solution_buf, 1);
      if (sol_vec[0].solved) {
        const GpuSolution &s = sol_vec[0];
        const quat4 d_qi = RotationVectorToQuat(vec3{s.w_inner.x, s.w_inner.y, s.w_inner.z});
        const quat4 qi = yocto::normalize(d_qi * s.q_outer);
        const frame3 outer_frame = yocto::rotation_frame(s.q_outer);
        const frame3 inner_frame =
            yocto::translation_frame(vec3{s.t_inner.x, s.t_inner.y, 0.0}) *
            yocto::rotation_frame(qi);

        const auto cl_val = GetClearance(poly, outer_frame, inner_frame);
        if (cl_val.has_value() && cl_val.value() > 0.0) {
          status.Clear();
          Print("\n" AGREEN("==================================================") "\n"
                AWHITE("GPU FOUND VERIFIED SOLUTION FOR {}!") "\n"
                AYELLOW("Exact 3D Clearance: {:.17g}") "\n"
                "Outer poses tested: {}\n"
                "Search trajectories: {}\n"
                "Time: {}\n"
                AGREEN("==================================================") "\n\n",
                poly.name,
                cl_val.value(),
                total_outer_poses,
                total_trajectories,
                ANSI::Time(run_timer.Seconds()));

          const auto ratio_val = GetRatio(poly, outer_frame, inner_frame);
          if (ratio_val.has_value()) {
            db->AddSolution(poly.name, outer_frame, inner_frame,
                            SolutionDB::METHOD_TILT_GPU, 0,
                            ratio_val.value(), cl_val.value());
          }
          FlushAttempts();
          return;
        }
      }

      // Inspect the top candidate to see if we should try joint
      // optimization on the CPU.
      const auto cand_vec = CopyBufferFromGPU<GpuCandidate>(
          cl->queue, candidates_buf, batch_size * threads_per_pose);

      int best_cand_idx = 0;
      double batch_best_clearance = -1e30;
      for (size_t c = 0; c < cand_vec.size(); c++) {
        if (cand_vec[c].clearance > batch_best_clearance) {
          batch_best_clearance = cand_vec[c].clearance;
          best_cand_idx = c;
        }
      }

      if (batch_best_clearance > highest_clearance_seen) {
        highest_clearance_seen = batch_best_clearance;
      }
      if (!unflushed_highest_clearance.has_value() ||
          batch_best_clearance > unflushed_highest_clearance.value()) {
        unflushed_highest_clearance = {batch_best_clearance};
      }

      if (batch_best_clearance > -5e-5) {
        const int outer_pose_idx = best_cand_idx / threads_per_pose;
        frame3 fo, fi;
        if (RefineCandidateCPU(host_outer_poses[outer_pose_idx],
                               cand_vec[best_cand_idx],
                               &fo, &fi)) {
          const auto cl_val = GetClearance(poly, fo, fi);
          if (cl_val.has_value() && cl_val.value() > 0.0) {
            status.Abandon();
            Print(
                "\n" AGREEN("==================================================") "\n"
                AWHITE("GPU + CPU POLISH FOUND VERIFIED SOLUTION FOR {}!") "\n"
                AYELLOW("Exact 3D Clearance: {:.17g}") "\n"
                "Outer poses tested: {}\n"
                "Search trajectories: {}\n"
                "Time: {}\n"
                AGREEN("==================================================") "\n\n",
                poly.name,
                cl_val.value(),
                total_outer_poses,
                total_trajectories,
                ANSI::Time(run_timer.Seconds()));

            const auto ratio_val = GetRatio(poly, fo, fi);
            if (ratio_val.has_value()) {
              db->AddSolution(poly.name, fo, fi,
                              SolutionDB::METHOD_TILT_GPU, 0,
                              ratio_val.value(), cl_val.value());
            }
            FlushAttempts();
            return;
          }
        }
      }

      if (flush_per.ShouldRun()) {
        FlushAttempts();
      }

      if (status_per.ShouldRun()) {
        const double sec = run_timer.Seconds();
        const double poses_per_sec = total_outer_poses / sec;
        const double trajs_per_sec = total_trajectories / sec;

        status.Status(
            "Batches: " AWHITE("{}") " | Poses: " APURPLE("{}") " (" ACYAN("{:.0f}") "/s) | "
            "Traj: " APURPLE("{}") " (" ACYAN("{:.0f}") "/s)"
            "\n"
            "Best c: " AGREEN("{:+.17g}") " | Time: {}",
            batch_num,
            FormatNum(total_outer_poses), poses_per_sec,
            FormatNum(total_trajectories), trajs_per_sec,
            highest_clearance_seen, ANSI::Time(sec));
      }
    }

    FlushAttempts();
  }

  static constexpr int STATUS_LINES = 2;

  ArcFour rc;
  SolutionDB *db = nullptr;
  const Polyhedron &poly;
  const int num_vertices;
  const int batch_size;
  const int threads_per_pose;
  const int max_steps;
  const bool forward_diff;
  std::vector<SeedPoint> seed_points;
  double seed_sigma = 0.001;

  StatusBar status;


  cl_program program = nullptr;
  cl_kernel tilt_kernel = nullptr;
  cl_mem base_verts_buf = nullptr;
  cl_mem outer_poses_buf = nullptr;
  cl_mem solution_buf = nullptr;
  cl_mem candidates_buf = nullptr;

  std::vector<GpuOuterPose> host_outer_poses;
};

int main(int argc, char **argv) {
  ANSI::Init();

  std::string poly_name = "snubcube";

  std::string seed_file;
  int batch_size = 256;
  int threads_per_pose = 64;
  int max_steps = 25;
  int iters = -1;
  double seed_sigma = 0.001;
  bool dump_ptx = false;
  bool forward_diff = true;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--poly" || arg == "-p") {
      CHECK(i + 1 < argc);
      poly_name = argv[++i];
    } else if (arg == "--seeds" || arg == "--seed-file") {
      CHECK(i + 1 < argc);
      seed_file = argv[++i];
    } else if (arg == "--sigma") {
      CHECK(i + 1 < argc);
      seed_sigma = std::stod(argv[++i]);
    } else if (arg == "--batch" || arg == "-b") {
      CHECK(i + 1 < argc);
      batch_size = std::stoi(argv[++i]);
    } else if (arg == "--threads" || arg == "-t") {
      CHECK(i + 1 < argc);
      threads_per_pose = std::stoi(argv[++i]);
    } else if (arg == "--steps" || arg == "-s") {
      CHECK(i + 1 < argc);
      max_steps = std::stoi(argv[++i]);
    } else if (arg == "--iters" || arg == "-n") {
      CHECK(i + 1 < argc);
      iters = std::stoi(argv[++i]);
    } else if (arg == "--dump-ptx" || arg == "-d") {
      dump_ptx = true;
    } else if (arg == "--forward-diff") {
      forward_diff = true;
    } else if (arg == "--central-diff") {
      forward_diff = false;

    } else if (arg == "--help" || arg == "-h") {
      Print("Usage: ./tiltperts.exe [options] [polyhedron_name]\n"
            "Options:\n"
            "  --poly, -p <name>      Polyhedron name (default: snubcube)\n"
            "  --seeds, --seed-file <f> Path to seed points file (e.g. seed-points229.txt)\n"
            "  --sigma <val>          Gaussian std dev for seed perturbation (default: 0.001)\n"
            "  --batch, -b <K>        Outer poses per batch (default: 256)\n"
            "  --threads, -t <W>      Search threads per pose (default: 64)\n"
            "  --steps, -s <N>        Gradient steps per trajectory (default: 25)\n"
            "  --iters, -n <M>        Max batches to run (-1 = infinite, default)\n"

            "  --forward-diff         Use forward differences (3 evals/step, default)\n"
            "  --central-diff         Use central differences (6 evals/step)\n"
            "  --dump-ptx, -d         Dump driver PTX/binary after build\n");
      return 0;


    } else if (arg[0] != '-') {
      poly_name = arg;
    }
  }

  cl = new CL;
  Print(AGREEN("OpenCL initialized successfully.") "\n");
  for (const auto &[k, v] : cl->DeviceInfo()) {
    Print(AWHITE("{}") ": {}\n", k, v);
  }
  Print("\n");

  std::vector<SeedPoint> seeds;

  if (!seed_file.empty()) {
    seeds = LoadSeedPoints(seed_file);
    if (poly_name == "snubcube") {
      poly_name = "nopert_229";
    }
  }


  SolutionDB db;
  if (poly_name == "229") {
    poly_name = "nopert_229";
  }
  Polyhedron target = db.AnyPolyhedronByName(poly_name);

  Print("Target polyhedron: " APURPLE("{}") " ({} vertices)\n",
         target.name, target.vertices.size());
  Print("Config: batch={}, threads_per_pose={}, steps={}, diff={}, sigma={}\n"
        "  (total work-items per launch: {})\n\n",
        batch_size, threads_per_pose, max_steps,
        forward_diff ? "forward (3 evals)" : "central (6 evals)",
        seed_sigma,
        batch_size * threads_per_pose);

  TiltGPU solver(&db, target, batch_size, threads_per_pose, max_steps, dump_ptx, forward_diff, seeds, seed_sigma);
  solver.Run(iters);



  delete cl;
  return 0;
}
