#include "tubeatlas5d.h"

#include <cstdio>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

using namespace tubeatlas5d;

static constexpr const char *MANIFEST = "../Noperthedron/.artifacts/nopert229r/packs_r2/manifest.txt";

int main() {
  if (!std::filesystem::exists("trees_r2/tree.0.json")) {
    printf("SKIPPED: trees_r2 not present\n");
    return 0;
  }
  const TubeAtlas atlas = TubeAtlas::Load("trees_r2", "codebdd229.json");
  CHECK(atlas.NumTriangles() == 153) << atlas.NumTriangles();

  // The root radius of each table equals the exported pack's table radius
  // (manifest: file code tri rows r), which Lean validated.
  if (std::filesystem::exists(MANIFEST)) {
    std::ifstream f(MANIFEST);
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
    CHECK(t == 153);
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
