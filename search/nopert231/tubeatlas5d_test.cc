#include "tubeatlas5d.h"

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

using namespace tubeatlas5d;

// Test data, not committed: refined identity-tube trees (rebuild.sh's
// trees_r2) in $TREES_DIR (default trees_r2), and codebdd's output in
// $CODEBDD_JSON (default codebdd.json). Without them the test is skipped.
static std::string EnvOr(const char *name, const char *dflt) {
  const char *e = getenv(name);
  return e != nullptr ? e : dflt;
}
// Optionally, $TUBE_MANIFEST is the tube packs' manifest.txt written by
// export_codetrees_pack from those trees.

int main() {
  const std::string trees = EnvOr("TREES_DIR", "trees_r2");
  const std::string bdd = EnvOr("CODEBDD_JSON", "codebdd.json");
  const std::string manifest = EnvOr("TUBE_MANIFEST", "");
  if (!std::filesystem::exists(trees + "/tree.0.json") || !std::filesystem::exists(bdd)) {
    printf("SKIPPED: %s/tree.0.json or %s not present\n", trees.c_str(), bdd.c_str());
    return 0;
  }
  const TubeAtlas atlas = TubeAtlas::Load(trees, bdd);
  const int num_tables = atlas.NumTriangles();
  CHECK(num_tables > 0);

  // The root radius of each table equals the exported pack's table radius
  // (manifest: file code tri rows r), which Lean validated.
  if (!manifest.empty() && std::filesystem::exists(manifest)) {
    std::ifstream f(manifest);
    std::string line;
    int t = 0;
    while (std::getline(f, line)) {
      std::istringstream ss(line);
      std::string file, r;
      int code, tri, rows;
      ss >> file >> code >> tri >> rows >> r;
      CHECK(atlas.CodeAndTriangle(t) == std::make_pair(code, tri)) << line;
      CHECK(atlas.Walk(t, "").r_lower == BigRat(std::string_view(r))) << line;
      t++;
    }
    CHECK(t == num_tables) << t;
    printf("  root radii match the pack manifest\n");
  }

  // The walk stops at a leaf; radii never decrease going down.
  int max_depth = 0;
  for (int t = 0; t < atlas.NumTriangles(); t++) {
    const std::string deep(40, '3');
    const auto r = atlas.Walk(t, deep);
    CHECK(r.depth < 40);
    max_depth = std::max(max_depth, r.depth);
    std::string prefix;
    BigRat prev = atlas.Walk(t, "").r_lower;
    for (int d = 0; d < r.depth; d++) {
      prefix += '3';
      const auto rd = atlas.Walk(t, prefix);
      CHECK(rd.depth == d + 1);
      CHECK(!(rd.r_lower < prev));
      prev = rd.r_lower;
    }
  }
  printf("  walks OK (deepest central path %d)\n", max_depth);
  printf("tubeatlas5d tests PASSED\n");
  return 0;
}
