// The identity tube, as the 5D search sees it: for each code triangle t (in
// WedgeCover.codeTriangles order: codes in codebdd.json order, their
// triangles in order), the tube tree certified for it, loaded from the
// native tree files (trees_dir/tree.<code>.json, as written by tubecode).
//
// A 5D leaf in code triangle t with view path P is ruled out up to radius
// rLower of the node Lean reaches walking P in that table
// (AtlasProjectiveLocalViewTree.Table.findNodePrefix): the walk follows
// children while it can and stops at a leaf or at the end of P. rLower is the
// minimum certificate radius r over the node's subtree, computed exactly as
// export-codetrees-pack writes it, so this matches the packed tables.

#ifndef _NOPERT_TUBEATLAS5D_H
#define _NOPERT_TUBEATLAS5D_H

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
  // The projective root of global triangle t (its code's "root" in the
  // BDD, 0 if absent; checked against the corners).
  int Root(int t) const { return tables_[t].root; }
  // The code and the triangle index within it, for global triangle t.
  std::pair<int, int> CodeAndTriangle(int t) const { return {tables_[t].code, tables_[t].tri}; }

  struct Reached {
    // How many digits of the path the walk consumed.
    int depth = 0;
    BigRat r_lower{0};
    // The largest certificate radius in the reached node's subtree: an
    // upper bound on the radius any further view refinement can certify.
    BigRat r_upper{0};
    // Whether the reached node is a leaf of the table.
    bool leaf = false;
  };
  // The node Lean reaches walking `path` (digits '0'..'3') from the root of
  // triangle t's table.
  Reached Walk(int t, std::string_view path) const;

 private:
  struct Node {
    int children[4] = {-1, -1, -1, -1};  // all -1 for a leaf
    BigRat r_lower{0};
    BigRat r_upper{0};
  };
  struct Table {
    int code = 0, tri = 0, root = 0;
    exact5d::TriangleQ triangle;
    std::vector<Node> nodes;  // nodes[0] is the root
  };
  std::vector<Table> tables_;
};

}  // namespace tubeatlas5d

#endif
