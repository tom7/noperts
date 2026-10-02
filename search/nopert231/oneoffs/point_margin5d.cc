// Best single-triple certificate margin at a pose as the box and the view
// triangle shrink around it: does the margin stay positive (subdivision
// terminates) or go to zero (a possible Rupert passage)?
//
// Usage: point_margin5d.exe <t> <chart> <view path> <x> <y> <z>

#include <cstdio>
#include <string>

#include "cert5d.h"
#include "contacts5d.h"
#include "geom5d.h"
#include "rows5d.h"
#include "solve5d.h"
#include "tubeatlas5d.h"

int main(int argc, char **argv) {
  const int t = std::stoi(argv[1]), chart = std::stoi(argv[2]);
  const std::string view = argv[3];
  const geom5d::vec3 w = {std::stod(argv[4]), std::stod(argv[5]), std::stod(argv[6])};
  const auto atlas = tubeatlas5d::TubeAtlas::Load("trees_r2", "codebdd231.json");
  const auto root = solve5d::RootNode(atlas, {.t = t, .chart = chart});
  printf("|w| = %.4g\n", yocto::length(w));
  for (int extra = 0; extra <= 8; extra += 4) {
    // Refine the view toward its center (child 3 is the central triangle).
    const std::string vp = view + std::string(extra, '3');
    const auto td = geom5d::ToDouble(rows5d::NodeTriangle(root.tri, vp));
    contacts5d::PoolParams params;
    const auto pool = contacts5d::BuildContactPool(td, params);
    printf("view %s (diam %.3g), %zu triples:", vp.c_str(), geom5d::AngularDiameter(td),
           pool.triples.size());
    for (double r : {1e-5, 1e-6, 1e-7, 1e-8, 1e-9}) {
      geom5d::BoxD bd{.center = w, .radius = {r, r, r}};
      const auto s = cert5d::BestSingle(pool, td, bd, chart, 256);
      const auto m = cert5d::BestMixture(pool, td, bd, chart, 4);
      printf("  r=%.0e: %.3g/%.3g", r, s.margin, m.margin);
    }
    printf("\n");
  }
  return 0;
}
