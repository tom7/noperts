// Prints the terms of the best single-certificate margin at given 5D nodes
// (and at the same box with the view one level coarser): displacement lower
// bound, defect charge, displacement error. For diagnosing why near-identity
// chart-0 boxes need deep views.
//
// Usage: margin_terms5d.exe <t> <chart> <path>...

#include <cstdio>
#include <string>

#include "cert5d.h"
#include "contacts5d.h"
#include "geom5d.h"
#include "rows5d.h"
#include "solve5d.h"
#include "tubeatlas5d.h"

static void Report(const char *label, const solve5d::Node &node, int chart) {
  contacts5d::PoolParams params;
  const auto td = geom5d::ToDouble(node.tri);
  const auto bd = geom5d::ToDouble(node.box);
  const auto pool = contacts5d::BuildContactPool(td, params);
  for (int full : {64, 256, 1024, 4096}) {
    const auto f = cert5d::BestSingle(pool, td, bd, chart, full);
    printf("  [max_full %d: %.4g]", full, f.margin);
  }
  printf("\n");
  const auto s = cert5d::BestSingle(pool, td, bd, chart, 64);
  if (s.triple < 0) {
    printf("  %s: no triple\n", label);
    return;
  }
  const auto &tr = pool.triples[s.triple];
  const double lower = cert5d::DisplacementLower(pool, tr, s.inner, td, bd, chart);
  printf("  %s: |c|=%.3g r=%.3g diam=%.3g margin %.4g = lower %.4g - dbound*wdu %.4g - err %.3g"
         "  (contact defects %.3g %.3g %.3g; inner %d %d %d vs outer %d %d %d)\n",
         label, yocto::length(bd.center), yocto::max(bd.radius), geom5d::AngularDiameter(td),
         s.margin, lower, bounds5d::DBound(bd) * tr.weighted_defect_upper,
         bounds5d::DisplacementError(bd), pool.contacts[tr.c[0]].defect,
         pool.contacts[tr.c[1]].defect, pool.contacts[tr.c[2]].defect, s.inner[0], s.inner[1],
         s.inner[2], pool.contacts[tr.c[0]].vertex, pool.contacts[tr.c[1]].vertex,
         pool.contacts[tr.c[2]].vertex);
}

int main(int argc, char **argv) {
  const int t = std::stoi(argv[1]), chart = std::stoi(argv[2]);
  const auto atlas = tubeatlas5d::TubeAtlas::Load("trees_r2", "codebdd229.json");
  const auto root = solve5d::RootNode(atlas, {.t = t, .chart = chart});
  for (int i = 3; i < argc; i++) {
    const std::string path = argv[i];
    printf("%s\n", path.c_str());
    solve5d::Node node{.path = path, .tri = rows5d::NodeTriangle(root.tri, path),
                       .box = rows5d::NodeBox(root.box, path)};
    Report("leaf  ", node, chart);
    // Drop the last view step.
    const size_t k = path.find_last_of("0123");
    if (k != std::string::npos) {
      std::string coarse = path.substr(0, k) + path.substr(k + 1);
      solve5d::Node c{.path = coarse, .tri = rows5d::NodeTriangle(root.tri, coarse),
                      .box = node.box};
      Report("coarse", c, chart);
    }
  }
  return 0;
}
