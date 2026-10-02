// Near-identity Rupert passage survey for any convex polyhedron.
//
// The stochastic solvers are nearly blind to Rupert passages very close to
// the identity pose (#214 and #229 have passages of rotation angle ~1e-6
// with clearance ~1e-10). Those exist exactly where the identity pose is
// not first-order rigid: at some outer view u, the first-order margin m(u)
// (rigidity-margin.h) is negative. This program surveys m(u) over all
// views:
//   (a) a quasi-uniform (Fibonacci) grid over the hemisphere (u and -u give
//       mirrored shadows);
//   (b) every face plane's edge-on great circle, at several offsets on each
//       side, since the margin is discontinuous there and the passages of
//       #214 and #229 sit just beside such circles. The robust margin
//       (eclipsed-side limit) is evaluated on the circles themselves;
// then refines the worst views locally and, with --search, runs the
// passage search (SearchPassage) at them. A positive clearance is a
// candidate Rupert passage, to be confirmed exactly.
//
// The polyhedron is scaled to circumradius 1, so margins are comparable
// (length per radian).
//
// Usage: polyrigidity.exe (--name snubdodecahedron | --nopert ID) [--grid N]
//          [--circle_samples N] [--threads N] [--worst K] [--search]
//   e.g. polyrigidity.exe --name deltoidalhexecontahedron --search
//        polyrigidity.exe --nopert 214 --search   (finds #214's passage)

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <format>
#include <limits>
#include <mutex>
#include <numbers>
#include <optional>
#include <string>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "geom/polyhedra.h"
#include "rigidity-margin.h"
#include "solutions.h"
#include "threadutil.h"
#include "timer.h"
#include "yocto-math.h"

using rigidity::vec3;

namespace {

struct View {
  double margin;
  vec3 u;
  vec3 axis;
  const char *where;  // "grid", "circle", "circle robust"
};

// The distinct face planes' unit normals (n and -n give the same circle).
std::vector<vec3> FacePlaneNormals(const Polyhedron &poly) {
  std::vector<vec3> normals;
  for (const auto &face : poly.faces->v) {
    const vec3 &a = poly.vertices[face[0]], &b = poly.vertices[face[1]], &c = poly.vertices[face[2]];
    const vec3 n = yocto::normalize(yocto::cross(b - a, c - a));
    bool dup = false;
    for (const vec3 &m : normals) dup = dup || std::abs(yocto::dot(m, n)) > 1 - 1e-12;
    if (!dup) normals.push_back(n);
  }
  return normals;
}

bool Near(const vec3 &a, const vec3 &b, double d) {
  return std::min(yocto::distance(a, b), yocto::distance(a, -b)) < d;
}

}  // namespace

int main(int argc, char **argv) {
  std::string name;
  int nopert = -1, grid = 200000, circle_samples = 20000, threads = 60, worst_k = 12;
  bool search = false;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a << " needs a value";
      return argv[++i];
    };
    if (a == "--name") name = next();
    else if (a == "--nopert") nopert = std::stoi(next());
    else if (a == "--grid") grid = std::stoi(next());
    else if (a == "--circle_samples") circle_samples = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--worst") worst_k = std::stoi(next());
    else if (a == "--search") search = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(name.empty() != (nopert < 0)) << "exactly one of --name, --nopert";

  std::vector<vec3> verts;
  std::string label;
  if (!name.empty()) {
    std::optional<Polyhedron> p = PolyhedronByName(name);
    CHECK(p.has_value()) << "unknown polyhedron " << name;
    verts = p->vertices;
    label = name;
  } else {
    SolutionDB db;
    verts = db.GetNopert(nopert).vertices;
    label = std::format("nopert_{}", nopert);
  }
  double rmax = 0;
  for (const vec3 &v : verts) rmax = std::max(rmax, yocto::length(v));
  for (vec3 &v : verts) v /= rmax;
  std::optional<Polyhedron> poly = PolyhedronFromVertices(verts, label);
  CHECK(poly.has_value()) << "not a convex polyhedron";
  const std::vector<vec3> normals = FacePlaneNormals(*poly);
  Print("{}: {} vertices, {} faces, {} distinct face planes\n", label, verts.size(),
        poly->faces->v.size(), normals.size());

  // The views.
  struct Job { vec3 u; bool on_circle; };
  std::vector<Job> jobs;
  const double golden = std::numbers::pi * (3 - std::sqrt(5.0));
  for (int i = 0; i < grid; i++) {
    const double z = (i + 0.5) / grid;  // upper hemisphere, area-uniform
    const double r = std::sqrt(std::max(0.0, 1 - z * z));
    jobs.push_back({vec3{r * std::cos(golden * i), r * std::sin(golden * i), z}, false});
  }
  const std::vector<double> offsets = {0.0, 1e-9, -1e-9, 1e-6, -1e-6, 1e-4, -1e-4,
                                       1e-3, -1e-3, 1e-2, -1e-2};
  for (const vec3 &n : normals) {
    const vec3 a = yocto::normalize(yocto::cross(n, std::abs(n.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0}));
    const vec3 b = yocto::cross(n, a);
    for (int s = 0; s < circle_samples; s++) {
      // Half the circle suffices (u ~ -u).
      const double t = std::numbers::pi * s / circle_samples;
      const vec3 u0 = a * std::cos(t) + b * std::sin(t);
      for (double off : offsets) jobs.push_back({yocto::normalize(u0 + n * off), off == 0.0});
    }
  }
  Print("{} views ({} grid, {} on/near edge-on circles)\n", jobs.size(), grid, jobs.size() - grid);

  Timer timer;
  std::vector<View> all(jobs.size());
  std::vector<View> robust(jobs.size(), View{std::numeric_limits<double>::infinity()});
  std::atomic<int64_t> done{0};
  ParallelComp(jobs.size(), [&](int64_t i) {
    const Job &job = jobs[i];
    const rigidity::Margin m = rigidity::FirstOrderMargin(verts, job.u, false);
    all[i] = View{m.m, job.u, m.axis, job.on_circle ? "circle" : (i < grid ? "grid" : "near circle")};
    if (job.on_circle) {
      const rigidity::Margin r = rigidity::FirstOrderMargin(verts, job.u, true);
      robust[i] = View{r.m, job.u, r.axis, "circle robust"};
    }
    const int64_t d = ++done;
    if (d % 2000000 == 0) Print("  {} / {} views ({:.0f}s)\n", d, jobs.size(), timer.Seconds());
  }, threads);
  Print("surveyed in {:.0f}s\n", timer.Seconds());

  // The worst distinct views, true and robust.
  auto worst_of = [&](std::vector<View> v) {
    std::sort(v.begin(), v.end(), [](const View &a, const View &b) { return a.margin < b.margin; });
    std::vector<View> out;
    for (const View &x : v) {
      if ((int)out.size() >= worst_k || !std::isfinite(x.margin)) break;
      bool near = false;
      for (const View &y : out) near = near || Near(x.u, y.u, 0.02);
      if (!near) out.push_back(x);
    }
    return out;
  };
  const std::vector<View> worst_true = worst_of(all);
  const std::vector<View> worst_robust = worst_of(robust);
  Print("worst robust margin (edge-on circles): {:+.4e} at u=({:.8f},{:.8f},{:.8f})\n",
        worst_robust.empty() ? 0.0 : worst_robust[0].margin, worst_robust[0].u.x,
        worst_robust[0].u.y, worst_robust[0].u.z);

  // Refine and (optionally) search for passages at the worst views.
  std::vector<View> candidates = worst_true;
  for (const View &v : worst_robust) candidates.push_back(v);
  std::mutex mu;
  double global_min = std::numeric_limits<double>::infinity();
  double best_clearance = -std::numeric_limits<double>::infinity();
  ParallelComp(candidates.size(), [&](int64_t k) {
    const View &v = candidates[k];
    const auto [rm, ru] = rigidity::RefineView(verts, v.u);
    const rigidity::Margin at = rigidity::FirstOrderMargin(verts, ru, false);
    std::string line = std::format("  [{}] margin {:+.4e} -> refined {:+.4e} at u=({:.9f},{:.9f},{:.9f}) "
                                   "axis ({:.5f},{:.5f},{:.5f})",
                                   v.where, v.margin, rm, ru.x, ru.y, ru.z, at.axis.x, at.axis.y, at.axis.z);
    double clearance = -std::numeric_limits<double>::infinity();
    if (search) {
      const rigidity::PassageResult pr = rigidity::SearchPassage(verts, ru, at.axis);
      clearance = pr.clearance;
      line += std::format("\n      passage search: best clearance {:+.4e} at theta {:.3e}, "
                          "u=({:.9f},{:.9f},{:.9f}) axis ({:.6f},{:.6f},{:.6f}){}",
                          pr.clearance, pr.theta, pr.u.x, pr.u.y, pr.u.z, pr.axis.x, pr.axis.y,
                          pr.axis.z, pr.clearance > 0 ? "  ** CANDIDATE PASSAGE **" : "");
    }
    std::lock_guard<std::mutex> l(mu);
    Print("{}\n", line);
    global_min = std::min(global_min, rm);
    best_clearance = std::max(best_clearance, clearance);
  }, std::min(threads, (int)candidates.size()));
  Print("{}: worst first-order margin {:+.4e}{}\n", label, global_min,
        search ? std::format("; best passage clearance {:+.4e}", best_clearance) : "");
  return 0;
}
