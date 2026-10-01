// Benchmark: exact certificate checks (exact5d, which mirrors Lean) over a
// leaf's exact view triangle vs. over geom5d::OuterDyadicTriangle of it.
// Usage: bench_relax5d.exe <journal> <t> <chart> [max_leaves] [rel_bits]

#include <chrono>
#include <cstdio>
#include <string>
#include <variant>

#include "base/logging.h"
#include "cert5d.h"
#include "contacts5d.h"
#include "exact5d.h"
#include "geom5d.h"
#include "rows5d.h"
#include "tubeatlas5d.h"

int main(int argc, char **argv) {
  CHECK(argc >= 4);
  const int t = std::stoi(argv[2]), chart = std::stoi(argv[3]);
  const int max_leaves = argc > 4 ? std::stoi(argv[4]) : 100;
  const int rel_bits = argc > 5 ? std::stoi(argv[5]) : 30;
  const auto atlas = tubeatlas5d::TubeAtlas::Load("trees_r1", "codebdd229.json");
  const rows5d::Journal j = rows5d::ReadJournal(argv[1]);
  double exact_s = 0.0, relax_s = 0.0;
  int n = 0, exact_ok = 0, relax_ok = 0;
  using clock = std::chrono::steady_clock;
  for (const auto &r : j.leaves) {
    const auto *l = std::get_if<rows5d::CertLeaf>(&r.leaf);
    if (l == nullptr) continue;
    // Spread the sample over the tree.
    if (std::hash<std::string>()(r.path) % 97 != 0) continue;
    const exact5d::TriangleQ tri = rows5d::NodeTriangle(atlas.Triangle(t), r.path);
    const geom5d::BoxQ box = rows5d::NodeBox(geom5d::RootBox(chart), r.path);
    contacts5d::PoolParams params;
    params.cone_samples = l->cone_samples;
    const auto pool = contacts5d::BuildContactPool(geom5d::ToDouble(tri), params);
    const cert5d::Single s{.triple = l->triple, .inner = l->inner};
    // Time only exact5d::Valid, the part that mirrors Lean's row check
    // (building the box, e.g. its support bound B, is the packer's work).
    const exact5d::GlobalBox exact_box = cert5d::ExactGlobalBox(pool, s, tri, box, chart);
    const exact5d::TriangleQ outer = geom5d::OuterDyadicTriangle(tri, rel_bits);
    CHECK(geom5d::TriangleContains(outer, tri));
    const exact5d::GlobalBox outer_box = cert5d::ExactGlobalBox(pool, s, outer, box, chart);
    auto t0 = clock::now();
    exact_ok += exact5d::Valid(exact_box);
    auto t1 = clock::now();
    auto t2 = clock::now();
    relax_ok += exact5d::Valid(outer_box);
    auto t3 = clock::now();
    exact_s += std::chrono::duration<double>(t1 - t0).count();
    relax_s += std::chrono::duration<double>(t3 - t2).count();
    if (++n >= max_leaves) break;
  }
  printf("%d leaves: exact %.1f ms/leaf (%d valid), outer dyadic %.1f ms/leaf (%d valid)\n", n,
         1000 * exact_s / n, exact_ok, 1000 * relax_s / n, relax_ok);
  return 0;
}
