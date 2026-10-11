// dfwhere: where are a 5D job's deferred leaves? For each df leaf of
// jobs/c<chart>/t<t>.journal: the view (normalized centroid) and its angular
// diameter, the Cayley box (center and half-widths), |w|, and the identity
// tube radius at the view. Diagnostic only.
//
// Usage: dfwhere.exe --chart C --t T [--every K] [--jobs DIR] [--trees_dir DIR] [--bdd codebdd.json]
#include <cstdio>
#include <string>
#include "base/logging.h"
#include "geom5d.h"
#include "rows5d.h"
#include "tubeatlas5d.h"
int main(int argc, char **argv) {
  std::string jobs = "jobs", trees = "trees_r2", bdd = "codebdd.json";
  int chart = 0, t = 0, every = 1;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--chart") chart = std::stoi(next());
    else if (a == "--t") t = std::stoi(next());
    else if (a == "--every") every = std::stoi(next());
    else if (a == "--jobs") jobs = next();
    else if (a == "--trees_dir") trees = next();
    else if (a == "--bdd") bdd = next();
    else LOG(FATAL) << "unknown argument " << a;
  }
  auto atlas = tubeatlas5d::TubeAtlas::Load(trees, bdd);
  auto j = rows5d::ReadJournal(jobs + "/c" + std::to_string(chart) + "/t" + std::to_string(t) + ".journal");
  auto [code, tri] = atlas.CodeAndTriangle(t);
  printf("job c%d t%d: code %d triangle %d\n", chart, t, code, tri);
  int n = 0;
  for (const auto &r : j.leaves) {
    if (!std::holds_alternative<rows5d::DeferredLeaf>(r.leaf)) continue;
    if (n++ % every) continue;
    const auto T = rows5d::NodeTriangle(atlas.Triangle(t), r.path);
    const auto B = rows5d::NodeBox(geom5d::RootBox(chart), r.path);
    const auto td = geom5d::ToDouble(T);
    const auto bd = geom5d::ToDouble(B);
    const auto u = yocto::normalize(td.corners[0] + td.corners[1] + td.corners[2]);
    const auto reached = atlas.Walk(t, rows5d::ViewPath(r.path));
    printf("u (%.6f %.6f %.6f) diam %.2e  w (%.5f %.5f %.5f) +- (%.1e %.1e %.1e) |w| %.4f  tube r %.3g\n",
           u.x, u.y, u.z, geom5d::AngularDiameter(td), bd.center.x, bd.center.y, bd.center.z,
           bd.radius.x, bd.radius.y, bd.radius.z, yocto::length(bd.center), reached.r_lower.ToDouble());
  }
  printf("%d deferred\n", n);
}
