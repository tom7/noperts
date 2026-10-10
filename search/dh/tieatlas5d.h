// The deltoidal hexecontahedron's tie tubes (tietube.cc output) as a lookup
// for the 5D search: for pinning normal n, code triangle t and a view path,
// the radius rho certified for every view of that node (the minimum over the
// tie tree's leaves below it; 0 if any is uncertified or missing).

#ifndef _NOPERT_TIEATLAS5D_H
#define _NOPERT_TIEATLAS5D_H

#include <map>
#include <string>
#include <string_view>
#include <vector>

#include "bignum/big.h"

namespace tieatlas5d {

class TieAtlas {
 public:
  // Loads dir/n<n>_t<t>.txt for every n < num_normals and t < num_triangles
  // (missing files: radius 0 everywhere).
  static TieAtlas Load(const std::string &dir, int num_normals, int num_triangles);
  int NumNormals() const { return num_normals_; }
  BigRat Radius(int n, int t, std::string_view view_path) const;

 private:
  struct Node {
    bool split = false;
    BigRat rho{0};      // leaf radius (0: uncertified)
    BigRat min_rho{0};  // min over the subtree's leaves
  };
  using Tree = std::map<std::string, Node>;
  int num_normals_ = 0, num_triangles_ = 0;
  std::vector<Tree> trees_;  // [n * num_triangles + t]
};

}  // namespace tieatlas5d

#endif
