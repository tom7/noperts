// First-order rigidity margin of the identity pose, for repairing #214.
//
// For an outer view direction u, rotate the inner copy by a small angle
// theta about a unit axis w (and translate it optimally in the view plane).
// To first order the best achievable clearance is -theta * f_u(w), where
//   f_u(w) = min_t max_j ( n_j . (P(w x v_j) + t) )
// over the silhouette constraints j = (hull vertex v_j, outward unit
// normal n_j of an adjacent hull edge). If f_u(w) > 0 for every w, no
// small rotation about any axis lets the inner shadow fit: the identity
// pose is first-order rigid at u. The margin
//   m(u) = min_{|w| = 1} f_u(w)
// is in length units per radian. Where m(u) < 0, there is a near-identity
// Rupert passage (this is how #229 fails; nopert229/notes/Q.md 1.8).
//
// f_u is convex and positively homogeneous in w, so any norm on w gives a
// margin with the same sign. We use the max-norm: minimizing f_u over each
// face of the cube |w|_inf = 1 is a small linear program (w has one
// coordinate fixed to +-1 and two in [-1, 1]; t is free), solved with a
// dense simplex. This max-norm margin is within a factor of sqrt(3) of the
// Euclidean one; we also report f_u(w*)/|w*| at the minimizer w*.
//
// "Robust" margin: the same, but ignoring vertices that lie on a
// silhouette edge (or whose exterior angle is below ~1e-7), e.g. quad
// vertices when the quad is edge-on. Lean's local certificates cannot use
// contacts at such vertices. It is also physically meaningful: at an
// edge-on view the robust margin equals the limit of the true margin from
// the side where those vertices are eclipsed, which is where #229's
// passages are.

#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <format>
#include <limits>
#include <map>
#include <mutex>
#include <numbers>
#include <optional>
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "geom/hull-2d.h"
#include "geom/polyhedra.h"
#include "opt/opt.h"
#include "rigidity-margin.h"
#include "util.h"
#include "solutions.h"
#include "threadutil.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

using namespace rigidity;

namespace {

// Root parameterization, as in repair214: four root vertices, each
// repeated around z five times; r1.z is derived so that the quad face is
// exactly planar.
std::optional<std::vector<vec3>> VerticesFromRoot(std::array<vec3, 4> root) {
  const vec3 &r0 = root[0], &r1 = root[1], &r2 = root[2];
  const double theta = -2.0 * std::numbers::pi / 5.0;
  const double ct = std::cos(theta), st = std::sin(theta);
  const vec3 r1_rot(ct * r1.x - st * r1.y, st * r1.x + ct * r1.y, r1.z);
  const double dx = r1_rot.x - r1.x, dy = r1_rot.y - r1.y;
  const double C1 = (r2.x - r0.x) * dy - (r2.y - r0.y) * dx;
  if (std::abs(C1) < 1e-9) return std::nullopt;
  const double C2 = (r2.z - r0.z) * ((r1.x - r0.x) * dy - (r1.y - r0.y) * dx);
  root[1].z = r0.z + C2 / C1;
  std::vector<vec3> v;
  for (int level = 0; level < 4; level++) {
    for (int k = 0; k < 5; k++) {
      const double a = 2.0 * std::numbers::pi * k / 5.0;
      const double c = std::cos(a), s = std::sin(a);
      v.emplace_back(c * root[level].x - s * root[level].y,
                     s * root[level].x + c * root[level].y, root[level].z);
    }
  }
  return v;
}

vec3 RotateZ(vec3 v, double a) {
  const double c = std::cos(a), s = std::sin(a);
  return vec3{c * v.x - s * v.y, s * v.x + c * v.y, v.z};
}

struct ViewReport {
  // Worst views, at least 0.02 rad apart (for refinement).
  std::vector<std::pair<double, vec3>> worst;
  double min_true = std::numeric_limits<double>::infinity();
  vec3 argmin_true{};
  vec3 axis_true{};
  double min_robust = std::numeric_limits<double>::infinity();
  vec3 argmin_robust{};
};

// Evaluates the margin on (a) a grid over the fundamental domain and (b)
// the edge-on great circle of one face per C5 orbit, at several offsets
// on each side. Robust margins are evaluated on the circles themselves.
struct Survey {
  int grid = 120;
  int circle_samples = 20000;
  std::vector<double> offsets = {0.0, 1e-9, -1e-9, 1e-6, -1e-6, 1e-4, -1e-4,
                                 1e-3, -1e-3, 1e-2, -1e-2};
  int threads = 16;
  bool verbose = true;

  ViewReport Run(const std::vector<vec3> &verts) const {
    auto poly = PolyhedronFromVertices(verts, "cand");
    CHECK(poly.has_value());
    // One face normal per C5 orbit (normals equal up to z-rotation).
    std::vector<vec3> normals;
    for (const auto &face : poly->faces->v) {
      vec3 n = yocto::normalize(yocto::cross(verts[face[1]] - verts[face[0]],
                                             verts[face[2]] - verts[face[0]]));
      bool dup = false;
      for (const vec3 &m : normals) {
        // Same orbit iff same z component and same horizontal length
        // (up to sign, since the circle is the same).
        if (std::abs(std::abs(m.z) - std::abs(n.z)) < 1e-9) dup = true;
      }
      if (!dup) normals.push_back(n);
    }

    struct Job { vec3 u; bool on_circle; int circle; };
    std::vector<Job> jobs;
    // (a) Grid: azimuth in [0, 72 deg], z in [0, 1] (area-uniform).
    for (int i = 0; i <= grid; i++) {
      for (int j = 0; j <= grid; j++) {
        const double phi = (2.0 * std::numbers::pi / 5.0) * i / grid;
        const double z = (double)j / grid;
        const double r = std::sqrt(std::max(0.0, 1 - z * z));
        jobs.push_back({vec3{r * std::cos(phi), r * std::sin(phi), z}, false, -1});
      }
    }
    // (b) Edge-on circles.
    for (int c = 0; c < (int)normals.size(); c++) {
      const vec3 &n = normals[c];
      vec3 a = std::abs(n.z) < 0.9 ? yocto::normalize(yocto::cross(n, vec3{0, 0, 1}))
                                   : yocto::normalize(yocto::cross(n, vec3{1, 0, 0}));
      vec3 b = yocto::cross(n, a);
      for (int s = 0; s < circle_samples; s++) {
        const double t = 2.0 * std::numbers::pi * s / circle_samples;
        const vec3 u0 = a * std::cos(t) + b * std::sin(t);
        for (double off : offsets) {
          jobs.push_back({yocto::normalize(u0 + n * off), off == 0.0, c});
        }
      }
    }

    ViewReport rep;
    std::mutex mu;
    std::atomic<size_t> next{0};
    std::vector<double> margins(jobs.size());
    ParallelFan(threads, [&](int) {
      ViewReport local;
      for (;;) {
        const size_t i = next.fetch_add(1);
        if (i >= jobs.size()) break;
        const Job &job = jobs[i];
        Margin mt = FirstOrderMargin(verts, job.u, false);
        margins[i] = mt.m;
        if (mt.m < local.min_true) {
          local.min_true = mt.m; local.argmin_true = job.u; local.axis_true = mt.axis;
        }
        if (job.on_circle) {
          Margin mr = FirstOrderMargin(verts, job.u, true);
          if (mr.m < local.min_robust) { local.min_robust = mr.m; local.argmin_robust = job.u; }
        }
      }
      std::lock_guard<std::mutex> l(mu);
      if (local.min_true < rep.min_true) {
        rep.min_true = local.min_true; rep.argmin_true = local.argmin_true;
        rep.axis_true = local.axis_true;
      }
      if (local.min_robust < rep.min_robust) {
        rep.min_robust = local.min_robust; rep.argmin_robust = local.argmin_robust;
      }
    });
    {
      std::vector<size_t> idx(jobs.size());
      for (size_t i = 0; i < idx.size(); i++) idx[i] = i;
      std::sort(idx.begin(), idx.end(), [&](size_t a, size_t b) { return margins[a] < margins[b]; });
      for (size_t i : idx) {
        if (rep.worst.size() >= 6) break;
        bool near = false;
        for (const auto &[m, u] : rep.worst) {
          // Views are equivalent under u -> -u.
          if (std::min(yocto::distance(u, jobs[i].u), yocto::distance(u, -jobs[i].u)) < 0.02) near = true;
        }
        if (!near) rep.worst.push_back({margins[i], jobs[i].u});
      }
    }
    if (verbose) {
      Print("  {} views ({} edge-on circles). min true margin {:+.4e} at u=({:.6f},{:.6f},{:.6f}) "
            "axis ({:.4f},{:.4f},{:.4f}); min robust (on circles) {:+.4e} at u=({:.6f},{:.6f},{:.6f})\n",
            jobs.size(), normals.size(), rep.min_true, rep.argmin_true.x, rep.argmin_true.y,
            rep.argmin_true.z, rep.axis_true.x, rep.axis_true.y, rep.axis_true.z,
            rep.min_robust, rep.argmin_robust.x, rep.argmin_robust.y, rep.argmin_robust.z);
    }
    return rep;
  }
};


// Root perturbation parameters, in absolute length units (so a single
// parameter of size d moves the affected ring's vertices by about d).
// Ring 0's azimuth is fixed (global rotation); ring 1's z is derived to
// keep the quads planar.
// The last three are a global similarity (rotation about z, uniform
// scale, z shift). They don't change the margin (up to its scale) but
// do change how far the vertices move from #214, and Rupertness is
// invariant under them.
constexpr int kNumParams = 13;
const char *const kParamNames[kNumParams] = {
  "ring0 radial", "ring0 z",
  "ring1 radial", "ring1 tangential",
  "ring2 radial", "ring2 tangential", "ring2 z",
  "ring3 radial", "ring3 tangential", "ring3 z",
  "global rotation", "global scale", "global z shift",
};

std::array<vec3, 4> PerturbRoot(std::array<vec3, 4> r, const std::array<double, kNumParams> &d) {
  auto Radial = [](vec3 v, double dr) {
    const double rr = std::hypot(v.x, v.y);
    const double s = (rr + dr) / rr;
    return vec3{v.x * s, v.y * s, v.z};
  };
  auto Tangential = [](vec3 v, double dt) {
    return RotateZ(v, dt / std::hypot(v.x, v.y));
  };
  r[0] = Radial(r[0], d[0]); r[0].z += d[1];
  r[1] = Tangential(Radial(r[1], d[2]), d[3]);
  r[2] = Tangential(Radial(r[2], d[4]), d[5]); r[2].z += d[6];
  r[3] = Tangential(Radial(r[3], d[7]), d[8]); r[3].z += d[9];
  // Global similarity; d[10] is an arc length at unit radius, d[11] a
  // scale change times unit length.
  for (vec3 &v : r) {
    v = RotateZ(v, d[10]);
    v = v * (1.0 + d[11]);
    v.z += d[12];
  }
  return r;
}

double MaxVertexMove(const std::vector<vec3> &a, const std::vector<vec3> &b) {
  double mx = 0;
  for (size_t i = 0; i < a.size(); i++) mx = std::max(mx, yocto::distance(a[i], b[i]));
  return mx;
}

bool Is20V27F(const std::vector<vec3> &v) {
  auto poly = PolyhedronFromVertices(v, "cand");
  if (!poly.has_value() || poly->vertices.size() != 20 || poly->faces->v.size() != 27) return false;
  int c3 = 0, c4 = 0, c5 = 0;
  for (const auto &f : poly->faces->v) {
    if (f.size() == 3) c3++;
    else if (f.size() == 4) c4++;
    else if (f.size() == 5) c5++;
  }
  return c3 == 20 && c4 == 5 && c5 == 2;
}

// Worst (refined) true margin over all views, and where.
std::pair<double, vec3> WorstMargin(const std::vector<vec3> &v, int circle_samples) {
  Survey sv;
  sv.circle_samples = circle_samples;
  sv.verbose = false;
  ViewReport rep = sv.Run(v);
  double w = rep.min_robust;
  vec3 wu = rep.argmin_robust;
  for (const auto &[m, u] : rep.worst) {
    auto [rm, ru] = RefineView(v, u);
    if (rm < w) { w = rm; wu = ru; }
  }
  return {w, wu};
}

std::optional<std::array<vec3, 4>> ReadRootFile(const std::string &filename) {
  std::array<vec3, 4> root;
  int found = 0;
  for (const std::string &line : Util::ReadFileToLines(filename)) {
    std::vector<std::string> tok = Util::Tokens(line, [](char c) { return c == ' '; });
    if (tok.size() == 4 && tok[0].size() == 5 && tok[0].rfind("root", 0) == 0) {
      const int k = tok[0][4] - '0';
      if (k < 0 || k > 3) return std::nullopt;
      root[k] = vec3{std::stod(tok[1]), std::stod(tok[2]), std::stod(tok[3])};
      found |= 1 << k;
    }
  }
  if (found != 15) return std::nullopt;
  return root;
}

}  // namespace

int main(int argc, char **argv) {
  SolutionDB db;
  Polyhedron p214 = db.AnyPolyhedronByName("nopert_214");
  const std::array<vec3, 4> base = {p214.vertices[0], p214.vertices[5],
                                    p214.vertices[10], p214.vertices[15]};

  // Sanity check at the known #229 canyon view (Lean frame differs from
  // the DB frame only by scale), where canyon_passage measured
  // clearance/theta = +1.28e-5, i.e. margin ~ -1.28e-5 / 0.9763.
  std::array<vec3, 4> m9b = base;
  m9b[1] = RotateZ(m9b[1], -1.5e-3);
  m9b[2].x *= 1.0015; m9b[2].y *= 1.0015;
  m9b[3].z -= 1.5e-3;
  auto v229 = VerticesFromRoot(m9b);
  CHECK(v229.has_value());
  const vec3 canyon{0.915693739367, 0.203034665309, 0.346816810964};
  Margin mc = FirstOrderMargin(*v229, canyon, false);
  Print("M9b (#229) at canyon view: margin (cube) {:+.4e}, euclid-upper {:+.4e}, "
        "axis ({:.5f},{:.5f},{:.5f})\n",
        mc.m, mc.m_euclid_upper, mc.axis.x, mc.axis.y, mc.axis.z);

  auto v214 = VerticesFromRoot(base);
  CHECK(v214.has_value());

  if (argc > 1 && std::string(argv[1]) == "--selftest") {
    // Compare the cube-LP margin with a slow Euclidean reference: minimize
    // f over sampled unit axes (each f by an independent LP), then refine.
    auto Reference = [](const std::vector<Constraint> &cons) {
      const int N = 20000;
      double best = std::numeric_limits<double>::infinity();
      vec3 bw{0, 0, 1};
      for (int i = 0; i < N; i++) {
        const double z = 1 - 2 * (i + 0.5) / N, r = std::sqrt(1 - z * z);
        const double phi = i * 2.399963229728653;
        const vec3 w{r * std::cos(phi), r * std::sin(phi), z};
        const double v = EvalF(cons, w);
        if (v < best) { best = v; bw = w; }
      }
      for (double step = 0.02; step > 1e-9; step *= 0.5) {
        for (bool improved = true; improved;) {
          improved = false;
          for (int k = 0; k < 6; k++) {
            vec3 w = bw;
            w[k / 2] += (k & 1) ? -step : step;
            w = yocto::normalize(w);
            const double v = EvalF(cons, w);
            if (v < best) { best = v; bw = w; improved = true; }
          }
        }
      }
      return best;
    };
    struct Case { const char *name; const std::vector<vec3> *v; vec3 u; bool robust; };
    std::vector<Case> cases = {{"M9b canyon", &*v229, canyon, false}};
    uint64_t st = 12345;
    auto Rnd = [&]() { st = st * 6364136223846793005ULL + 1442695040888963407ULL;
                       return (double)(st >> 11) / 9007199254740992.0 * 2 - 1; };
    for (int i = 0; i < 12; i++) {
      cases.push_back({"#214 random", &*v214, yocto::normalize(vec3{Rnd(), Rnd(), Rnd()}),
                       (i % 3) == 0});
    }
    int bad = 0;
    for (const Case &c : cases) {
      const auto cons = SilhouetteConstraints(*c.v, c.u, c.robust);
      const Margin m = FirstOrderMargin(*c.v, c.u, c.robust);
      const double ref = Reference(cons);
      const double scale = std::max(1e-12, std::abs(m.m));
      std::string why;
      // (1)+(2): each face LP is consistent with an independent evaluation
      // of f at its minimizer, and no grid point on the face beats it.
      for (int face = 0; face < 3; face++) {
        for (double sign : {1.0, -1.0}) {
          const auto [v, w] = MinOnCubeFace(cons, face, sign);
          if (std::abs(EvalF(cons, w) - v) > 1e-10 * std::max(1.0, std::abs(v)))
            why += " inconsistent-minimizer";
          const int G = 60;
          for (int i = 0; i <= G; i++) {
            for (int j = 0; j <= G; j++) {
              vec3 g;
              g[face] = sign;
              g[(face + 1) % 3] = -1 + 2.0 * i / G;
              g[(face + 2) % 3] = -1 + 2.0 * j / G;
              if (EvalF(cons, g) < v - 1e-10 * std::max(1.0, std::abs(v)))
                why += " grid-beats-LP";
            }
          }
        }
      }
      // (3): signs agree; norm relations between cube (m_inf) and
      // Euclidean (m_2 <= both upper bounds) margins.
      if ((m.m > 0) != (ref > 0) || (m.m > 0) != (m.m_euclid_upper > 0)) why += " sign";
      const double up = std::min(ref, m.m_euclid_upper);
      if (m.m > 0 && (m.m_euclid_upper > m.m + 1e-12 || m.m > std::sqrt(3.0) * up + 1e-12))
        why += " norm-relation";
      if (m.m < 0 && m.m > m.m_euclid_upper + 1e-12) why += " norm-relation";
      (void)scale;
      if (!why.empty()) bad++;
      Print("{} {} u=({:+.4f},{:+.4f},{:+.4f}): cube {:+.6e}, euclid-upper {:+.6e}, "
            "sampled {:+.6e} {}\n", c.name, c.robust ? "robust" : "true", c.u.x, c.u.y,
            c.u.z, m.m, m.m_euclid_upper, ref, why.empty() ? "OK" : "FAIL:" + why);
    }
    Print("{}\n", bad == 0 ? "selftest OK" : "selftest FAILED");
    return bad == 0 ? 0 : 1;
  }

  if (argc > 6 && std::string(argv[1]) == "--view") {
    std::array<double, kNumParams> dp{};
    dp[atoi(argv[2])] = atof(argv[3]);
    auto v = VerticesFromRoot(PerturbRoot(base, dp));
    const vec3 u = yocto::normalize(vec3{atof(argv[4]), atof(argv[5]), atof(argv[6])});
    vec3 axis = std::abs(u.x) < std::abs(u.y)
        ? (std::abs(u.x) < std::abs(u.z) ? vec3{1, 0, 0} : vec3{0, 0, 1})
        : (std::abs(u.y) < std::abs(u.z) ? vec3{0, 1, 0} : vec3{0, 0, 1});
    const vec3 f = yocto::normalize(yocto::cross(u, axis)), g = yocto::cross(u, f);
    std::vector<vec2> p(20);
    for (int k = 0; k < 20; k++) p[k] = vec2{yocto::dot((*v)[k], f), yocto::dot((*v)[k], g)};
    std::vector<int> hull = Hull2D::QuickHull(p);
    Print("QuickHull ({}):", hull.size());
    for (size_t i = 0; i < hull.size(); i++) {
      const vec2 &a = p[hull[(i + hull.size() - 1) % hull.size()]], &b = p[hull[i]],
                 &c = p[hull[(i + 1) % hull.size()]];
      Print(" {}[{:+.2e}]", hull[i], Cross2(b - a, c - b));
    }
    Print("\n");
    for (bool robust : {false, true}) {
      Margin m = FirstOrderMargin(*v, u, robust);
      Print("{}: cube {:+.4e} euclid-upper {:+.4e} #cons {}\n", robust ? "robust" : "true",
            m.m, m.m_euclid_upper, SilhouetteConstraints(*v, u, robust).size());
    }
    return 0;
  }

  if (argc > 3 && std::string(argv[1]) == "--param") {
    std::array<double, kNumParams> dp{};
    dp[atoi(argv[2])] = atof(argv[3]);
    auto v = VerticesFromRoot(PerturbRoot(base, dp));
    CHECK(v.has_value());
    auto poly = PolyhedronFromVertices(*v, "cand");
    std::map<int, int> sizes;
    for (const auto &f : poly->faces->v) sizes[f.size()]++;
    std::string fs;
    for (auto [k, c] : sizes) fs += std::format(" {}x{}", c, k);
    Print("vertices {} faces:{}  max move {:.3e}\n", poly->vertices.size(), fs,
          MaxVertexMove(*v, *v214));
    Survey sv;
    sv.circle_samples = 2000;
    ViewReport rep = sv.Run(*v);
    for (const auto &[m, u] : rep.worst) {
      auto [rm, ru] = RefineView(*v, u);
      Margin mr = FirstOrderMargin(*v, ru, false);
      Print("  worst {:+.3e} at ({:+.5f},{:+.5f},{:+.5f}) -> refined {:+.4e} at ({:+.6f},{:+.6f},{:+.6f}) "
            "#cons {} axis ({:+.4f},{:+.4f},{:+.4f})\n", m, u.x, u.y, u.z, rm, ru.x, ru.y, ru.z,
            SilhouetteConstraints(*v, ru, false).size(), mr.axis.x, mr.axis.y, mr.axis.z);
    }
    return 0;
  }

  if (argc > 5 && std::string(argv[1]) == "--margin-at") {
    // Margins and silhouette at one view for a candidate root file.
    auto root = ReadRootFile(argv[2]);
    CHECK(root.has_value());
    auto v = VerticesFromRoot(*root);
    const vec3 u = yocto::normalize(vec3{atof(argv[3]), atof(argv[4]), atof(argv[5])});
    for (bool robust : {false, true}) {
      const Margin m = FirstOrderMargin(*v, u, robust);
      Print("{}: margin (cube) {:+.4e}, euclid-upper {:+.4e}, axis ({:+.4f},{:+.4f},{:+.4f}), #cons {}\n",
            robust ? "robust" : "true  ", m.m, m.m_euclid_upper, m.axis.x, m.axis.y, m.axis.z,
            SilhouetteConstraints(*v, u, robust).size());
    }
    auto [rm, ru] = RefineView(*v, u);
    Print("local min of true margin nearby: {:+.4e} at ({:+.7f},{:+.7f},{:+.7f})\n", rm, ru.x, ru.y, ru.z);
    return 0;
  }

  if (argc > 2 && std::string(argv[1]) == "--screen") {
    // Screen a candidate (root file) for near-identity passages.
    auto root = ReadRootFile(argv[2]);
    CHECK(root.has_value()) << "Bad root file " << argv[2];
    auto v = VerticesFromRoot(*root);
    CHECK(v.has_value());
    const int samples = argc > 3 ? atoi(argv[3]) : 50000;
    Print("Candidate {}: 20V/27F {}, max vertex move from #214 {:.4e}\n", argv[2],
          Is20V27F(*v) ? "yes" : "NO", MaxVertexMove(*v, *v214));
    Survey sv;
    sv.circle_samples = samples;
    ViewReport rep = sv.Run(*v);
    double worst = std::numeric_limits<double>::infinity();
    double best_clear = -std::numeric_limits<double>::infinity();
    for (const auto &[m, u] : rep.worst) {
      auto [rm, ru] = RefineView(*v, u);
      const Margin mm = FirstOrderMargin(*v, ru, false);
      const Margin mr = FirstOrderMargin(*v, ru, true);
      worst = std::min(worst, rm);
      PassageResult pr = SearchPassage(*v, ru, mm.axis);
      best_clear = std::max(best_clear, pr.clearance);
      Print("  view ({:+.6f},{:+.6f},{:+.6f}): margin true {:+.4e} robust {:+.4e}; "
            "best passage clearance {:+.4e} (theta {:.2e}, axis ({:+.4f},{:+.4f},{:+.4f}))\n",
            ru.x, ru.y, ru.z, rm, mr.m, pr.clearance, pr.theta, pr.axis.x, pr.axis.y, pr.axis.z);
    }
    // Genuine near-identity passages seen so far have clearance >= ~5e-12;
    // the difference-form evaluation is accurate far below that.
    constexpr double kPassageThreshold = 1e-14;
    Print("SCREEN {}: worst margin {:+.4e}, best passage clearance {:+.4e} -> {}\n", argv[2],
          worst, best_clear,
          best_clear > kPassageThreshold ? "PASSAGE FOUND (Rupert)" : "no passage found");
    return 0;
  }

  if (argc > 3 && std::string(argv[1]) == "--optimize") {
    // Maximize the worst margin subject to a vertex-move budget D.
    const double D = atof(argv[2]);
    const int iters = atoi(argv[3]);
    const int seed = argc > 4 ? atoi(argv[4]) : 12345;
    const int opt_samples = argc > 5 ? atoi(argv[5]) : 2000;
    std::array<double, kNumParams> lb, ub;
    lb.fill(-D);
    ub.fill(D);
    double best_j = -std::numeric_limits<double>::infinity();
    int evals = 0;
    auto F = [&](const std::array<double, kNumParams> &dp) -> double {
      evals++;
      auto v = VerticesFromRoot(PerturbRoot(base, dp));
      if (!v.has_value() || !Is20V27F(*v)) return 1.0;
      const double move = MaxVertexMove(*v, *v214);
      const double j = WorstMargin(*v, opt_samples).first;
      const double penalty = 10.0 * std::max(0.0, move - D);
      if (move <= D && j > best_j) {
        best_j = j;
        std::string ps;
        for (double x : dp) ps += std::format(" {:+.3e}", x);
        Print("[eval {}] worst margin {:+.4e}, max move {:.3e}, params{}\n", evals, j, move, ps);
        fflush(stdout);
      }
      return -j + penalty;
    };
    auto [best, val] = Opt::Minimize<kNumParams>(F, lb, ub, iters, 1, 1, seed);
    auto v = VerticesFromRoot(PerturbRoot(base, best));
    CHECK(v.has_value());
    const auto [wj, wu] = WorstMargin(*v, 20000);
    std::string out = std::format("# repair-margin --optimize {} {} {} {}\n# worst margin (20000/circle) {:+.6e} at "
                                  "u=({:+.9f},{:+.9f},{:+.9f}), max vertex move {:.6e}\nparams",
                                  D, iters, seed, opt_samples, wj, wu.x, wu.y, wu.z,
                                  MaxVertexMove(*v, *v214));
    for (double x : best) out += std::format(" {:.17g}", x);
    out += "\n";
    auto root = PerturbRoot(base, best);
    // Write the root with root1.z already derived (quad exactly planar),
    // as used for the vertices.
    root[1].z = (*v)[5].z;
    for (int i = 0; i < 4; i++)
      out += std::format("root{} {:.17g} {:.17g} {:.17g}\n", i, root[i].x, root[i].y, root[i].z);
    Print("{}", out);
    Util::WriteFile(std::format("repair-margin-best-{}-s{}.txt", D, seed), out);
    return 0;
  }

  if (argc > 1 && std::string(argv[1]) == "--sensitivity") {
    // Worst (refined) true margin for single-parameter moves of #214.
    Survey sv;
    sv.circle_samples = 2000;
    sv.verbose = false;
    auto Worst = [&](const std::vector<vec3> &v) {
      ViewReport rep = sv.Run(v);
      double w = std::numeric_limits<double>::infinity();
      vec3 wu{};
      for (const auto &[m, u] : rep.worst) {
        auto [rm, ru] = RefineView(v, u);
        if (rm < w) { w = rm; wu = ru; }
      }
      return std::make_pair(w, wu);
    };
    auto [w0, u0] = Worst(*v214);
    Print("#214 baseline: worst margin {:+.4e} at u=({:+.6f},{:+.6f},{:+.6f})\n", w0, u0.x, u0.y, u0.z);
    for (int p = 0; p < kNumParams; p++) {
      std::string line = std::format("{:>18}:", kParamNames[p]);
      for (double d : {-7.6e-4, -3e-4, -1e-4, 1e-4, 3e-4, 7.6e-4}) {
        std::array<double, kNumParams> dp{};
        dp[p] = d;
        auto v = VerticesFromRoot(PerturbRoot(base, dp));
        if (!v.has_value()) { line += "   (fail)  "; continue; }
        line += std::format(" {:+.0e}:{:+.2e}", d, Worst(*v).first);
      }
      Print("{}\n", line);
    }
    return 0;
  }

  Survey survey;
  if (argc > 1) survey.circle_samples = atoi(argv[1]);
  Print("#214 (idealized):\n");
  survey.Run(*v214);
  Print("M9b (#229):\n");
  survey.Run(*v229);
  return 0;
}
