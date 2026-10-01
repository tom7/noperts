#include "tubeatlas5d.h"

#include <format>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "rapidjson/document.h"
#include "tubetree229.h"
#include "util.h"

namespace tubeatlas5d {

namespace {

// Flattens a tree, computing each node's subtree-minimum certificate radius.
// Returns the index of `node` in `out`.
int Flatten(const tubetree229::TreeNode &node, std::vector<BigRat> *r_lower,
            std::vector<std::array<int, 4>> *children) {
  const int idx = r_lower->size();
  r_lower->push_back(BigRat(0));
  children->push_back({-1, -1, -1, -1});
  if (node.children.size() == 4) {
    BigRat r;
    for (int c = 0; c < 4; c++) {
      CHECK(node.children[c] != nullptr) << "missing child of " << node.path;
      const int ci = Flatten(*node.children[c], r_lower, children);
      (*children)[idx][c] = ci;
      r = (c == 0) ? (*r_lower)[ci] : BigRat::Min(r, (*r_lower)[ci]);
    }
    (*r_lower)[idx] = r;
  } else {
    CHECK(node.direct_cert.has_value() || node.decomposed_cert.has_value())
        << "uncertified leaf " << node.path;
    (*r_lower)[idx] = node.direct_cert.has_value() ? node.direct_cert->r : node.decomposed_cert->r;
  }
  return idx;
}

}  // namespace

TubeAtlas TubeAtlas::Load(const std::string &trees_dir, const std::string &bdd_json) {
  rapidjson::Document doc;
  doc.Parse(Util::ReadFile(bdd_json).c_str());
  CHECK(!doc.HasParseError()) << bdd_json;
  TubeAtlas atlas;
  const auto &codes = doc["codes"];
  for (rapidjson::SizeType code = 0; code < codes.Size(); code++) {
    const std::string path = std::format("{}/tree.{}.json", trees_dir, code);
    auto tree = tubetree229::LoadCodeTreeJson(path);
    CHECK(tree != nullptr) << "cannot load " << path;
    const auto &tris = codes[code]["triangles"];
    CHECK(tree->triangles.size() == tris.Size()) << path;
    for (rapidjson::SizeType t = 0; t < tris.Size(); t++) {
      Table table;
      table.code = code;
      table.tri = t;
      for (int i = 0; i < 3; i++) {
        table.triangle[i] = {BigRat(std::string_view(tris[t][i]["x"].GetString())),
                             BigRat(std::string_view(tris[t][i]["y"].GetString())),
                             BigRat(std::string_view(tris[t][i]["z"].GetString()))};
        const BigVecQ3 &tc = tree->triangles[t].triangle.corners[i];
        CHECK(tc.x == table.triangle[i][0] && tc.y == table.triangle[i][1] &&
              tc.z == table.triangle[i][2])
            << "tree triangle differs from the code triangle: code " << code << " tri " << t;
      }
      CHECK(tree->triangles[t].root != nullptr) << path;
      std::vector<BigRat> r_lower;
      std::vector<std::array<int, 4>> children;
      Flatten(*tree->triangles[t].root, &r_lower, &children);
      table.nodes.resize(r_lower.size());
      for (size_t n = 0; n < r_lower.size(); n++) {
        table.nodes[n].r_lower = r_lower[n];
        for (int c = 0; c < 4; c++) table.nodes[n].children[c] = children[n][c];
      }
      atlas.tables_.push_back(std::move(table));
    }
  }
  return atlas;
}

TubeAtlas::Reached TubeAtlas::Walk(int t, std::string_view path) const {
  CHECK(t >= 0 && t < (int)tables_.size());
  const Table &table = tables_[t];
  int node = 0, depth = 0;
  for (char ch : path) {
    CHECK(ch >= '0' && ch <= '3');
    const int child = table.nodes[node].children[ch - '0'];
    if (child < 0) break;
    node = child;
    depth++;
  }
  return Reached{.depth = depth, .r_lower = table.nodes[node].r_lower};
}

}  // namespace tubeatlas5d
