// The identity tube, as the 5D search sees it: for each code triangle t (in
// WedgeCover.codeTriangles order: codes in codebdd229.json order, their
// triangles in order), the tube tree certified for it, loaded from the
// native tree files (trees_dir/tree.<code>.json, as written by tubecode229).
//
// A 5D leaf in code triangle t with view path P is ruled out up to radius
// rLower of the node Lean reaches walking P in that table
// (AtlasProjectiveLocalViewTree.Table.findNodePrefix): the walk follows
// children while it can and stops at a leaf or at the end of P. rLower is the
// minimum certificate radius r over the node's subtree, computed exactly as
// export_codetrees_pack writes it, so this matches the packed tables.

#ifndef _NOPERT229_TUBEATLAS5D_H
#define _NOPERT229_TUBEATLAS5D_H

#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "bignum/big.h"
#include "exact5d.h"

namespace tubeatlas5d {

class TubeAtlas {
 public:
  // Loads every code's tree. Fails (CHECK) if a tree is missing or its base
  // triangle differs from the code triangle in bdd_json.
  static TubeAtlas Load(const std::string &trees_dir, const std::string &bdd_json);

  int NumTriangles() const { return (int)tables_.size(); }
  const exact5d::TriangleQ &Triangle(int t) const { return tables_[t].triangle; }
  // The code and the triangle index within it, for global triangle t.
  std::pair<int, int> CodeAndTriangle(int t) const { return {tables_[t].code, tables_[t].tri}; }

  struct Reached {
    // How many digits of the path the walk consumed.
    int depth = 0;
    BigRat r_lower{0};
  };
  // The node Lean reaches walking `path` (digits '0'..'3') from the root of
  // triangle t's table.
  Reached Walk(int t, std::string_view path) const;

 private:
  struct Node {
    int children[4] = {-1, -1, -1, -1};  // all -1 for a leaf
    BigRat r_lower{0};
  };
  struct Table {
    int code = 0, tri = 0;
    exact5d::TriangleQ triangle;
    std::vector<Node> nodes;  // nodes[0] is the root
  };
  std::vector<Table> tables_;
};

}  // namespace tubeatlas5d

#endif
