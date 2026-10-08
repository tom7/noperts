#include "tubeatlas5d.h"

#include <format>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "geom5d.h"
#include "rapidjson/document.h"
#include "tubetree.h"
#include "util.h"

namespace tubeatlas5d {

namespace {

// Flattens a tree, computing each node's subtree minimum and maximum
// certificate radius.
// Returns the index of `node` in the output arrays.
int Flatten(const tubetree::TreeNode &node, std::vector<BigRat> *r_lower,
            std::vector<BigRat> *r_upper, std::vector<std::array<int, 4>> *children) {
  const int idx = r_lower->size();
  r_lower->push_back(BigRat(0));
  r_upper->push_back(BigRat(0));
  children->push_back({-1, -1, -1, -1});
  if (node.children.size() == 4) {
    BigRat lo, hi;
    for (int c = 0; c < 4; c++) {
      CHECK(node.children[c] != nullptr) << "missing child of " << node.path;
      const int ci = Flatten(*node.children[c], r_lower, r_upper, children);
      (*children)[idx][c] = ci;
      lo = (c == 0) ? (*r_lower)[ci] : BigRat::Min(lo, (*r_lower)[ci]);
      hi = (c == 0) ? (*r_upper)[ci] : BigRat::Max(hi, (*r_upper)[ci]);
    }
    (*r_lower)[idx] = lo;
    (*r_upper)[idx] = hi;
  } else {
    // Cap leaves (tubetree::CapLeaf) certify no tube: the cap theorems cover their own
    // domains (cap leaves of the 5D search), and Lean's local tables give them rLower -1
    // (Row.empty), so no tube leaf may use them (radius 0 here).
    CHECK(node.has_certificate() || node.cap.has_value()) << "uncertified leaf " << node.path;
    const BigRat r = node.cap.has_value() ? BigRat(0) : node.GetCertifiedRadius();
    (*r_lower)[idx] = r;
    (*r_upper)[idx] = r;
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
    auto tree = tubetree::LoadCodeTreeJson(path);
    CHECK(tree != nullptr) << "cannot load " << path;
    const auto &tris = codes[code]["triangles"];
    CHECK(tree->triangles.size() == tris.Size()) << path;
    for (rapidjson::SizeType t = 0; t < tris.Size(); t++) {
      Table table;
      table.code = code;
      table.tri = t;
      table.root = codes[code].HasMember("root") ? codes[code]["root"].GetInt() : 0;
      for (int i = 0; i < 3; i++) {
        table.triangle[i] = {BigRat(std::string_view(tris[t][i]["x"].GetString())),
                             BigRat(std::string_view(tris[t][i]["y"].GetString())),
                             BigRat(std::string_view(tris[t][i]["z"].GetString()))};
        const BigVecQ3 &tc = tree->triangles[t].triangle.corners[i];
        CHECK(tc.x == table.triangle[i][0] && tc.y == table.triangle[i][1] &&
              tc.z == table.triangle[i][2])
            << "tree triangle differs from the code triangle: code " << code << " tri " << t;
      }
      CHECK(geom5d::SignedTriangleValid(table.root, table.triangle))
          << "code " << code << " tri " << t << " is not in root " << table.root;
      CHECK(tree->triangles[t].root != nullptr) << path;
      std::vector<BigRat> r_lower, r_upper;
      std::vector<std::array<int, 4>> children;
      Flatten(*tree->triangles[t].root, &r_lower, &r_upper, &children);
      table.nodes.resize(r_lower.size());
      for (size_t n = 0; n < r_lower.size(); n++) {
        table.nodes[n].r_lower = r_lower[n];
        table.nodes[n].r_upper = r_upper[n];
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
  const Node &n = table.nodes[node];
  return Reached{.depth = depth, .r_lower = n.r_lower, .r_upper = n.r_upper,
                 .leaf = n.children[0] < 0};
}

}  // namespace tubeatlas5d
