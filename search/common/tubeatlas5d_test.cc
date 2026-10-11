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
#include "rapidjson/document.h"
#include "test_data.h"
#include "util.h"

using namespace tubeatlas5d;

// Usage: tubeatlas5d_test.exe [TREES_DIR [MANIFEST]]
//
// TREES_DIR (or $TREES_DIR) holds the tube trees (tree.<code>.json, e.g.
// tuberefine's output) for the code triangles of ./codebdd.json ($CODEBDD_JSON); MANIFEST
// (or $TUBE_MANIFEST) is export_codetrees_pack's manifest.txt for those
// trees. Without trees the test is skipped; without a manifest, the
// manifest check is.

// The total number of code triangles in bdd_json.
static int NumCodeTriangles(const std::string &bdd_json) {
  rapidjson::Document doc;
  doc.Parse(Util::ReadFile(bdd_json).c_str());
  CHECK(!doc.HasParseError()) << bdd_json;
  int n = 0;
  for (const auto &code : doc["codes"].GetArray()) n += code["triangles"].Size();
  return n;
}

static std::string ArgOrEnv(int argc, char **argv, int i, const char *env) {
  if (argc > i) return argv[i];
  const char *e = getenv(env);
  return e != nullptr ? e : "";
}

int main(int argc, char **argv) {
  const std::string trees_dir = ArgOrEnv(argc, argv, 1, "TREES_DIR");
  const std::string manifest = ArgOrEnv(argc, argv, 2, "TUBE_MANIFEST");
  if (trees_dir.empty() || !std::filesystem::exists(trees_dir + "/tree.0.json")) {
    printf("SKIPPED: no tube trees (pass TREES_DIR)\n");
    return 0;
  }
  if (!HaveCodebddJson("tubeatlas5d_test")) return 0;
  const TubeAtlas atlas = TubeAtlas::Load(trees_dir, CodebddJson());
  const int num_triangles = NumCodeTriangles(CodebddJson());
  CHECK(atlas.NumTriangles() == num_triangles) << atlas.NumTriangles();

  // The root radius of each table equals the exported pack's table radius
  // (manifest: file code tri rows r), which Lean validated.
  if (manifest.empty() || !std::filesystem::exists(manifest)) {
    printf("  SKIPPED manifest check (pass MANIFEST)\n");
  } else {
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
    CHECK(t == num_triangles);
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
