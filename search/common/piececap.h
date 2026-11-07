// Piece caps: a cap whose views are a union of convex cones, the "pieces",
// each a list of rational half spaces: n_0.P > 0, n_i.P >= 0 for i >= 1.
// A view triangle is in the cap iff all its corners are in one piece (test
// the pieces separately: their union need not be convex). Rotations: the
// Cayley ball |w|^2 <= wmax2 of chart 0.
//
// The file (search/<solid>/*.txt, passed by --piece_caps to tubecode and
// search5d) holds, per cap,
//   cap <wmax2>
//   piece <n_0 x y z> <n_1 x y z> ...     (rationals, one line per piece)
// In a tube tree or a 5D journal a piece cap's index comes after the other
// caps (--cap, or search5d's --caps and --trib_caps).

#ifndef _NOPERT_PIECECAP_H
#define _NOPERT_PIECECAP_H

#include <array>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace piececap {

using Q = BigRat;
using VecQ = std::array<Q, 3>;

struct Piece {
  std::vector<VecQ> normals;
  // The same in double (for screens).
  std::vector<std::array<double, 3>> normals_d;
};

struct PieceCap {
  Q wmax2;
  double wmax2_d = 0;
  std::vector<Piece> pieces;
};

inline bool InPiece(const Piece &piece, const Q &x, const Q &y, const Q &z) {
  for (size_t i = 0; i < piece.normals.size(); i++) {
    const VecQ &n = piece.normals[i];
    const Q d = n[0] * x + n[1] * y + n[2] * z;
    const int sign = Q::Sign(d);
    if (i == 0 ? sign <= 0 : sign < 0) return false;
  }
  return true;
}

// The index of a piece holding all of the corners (each with [0], [1], [2]
// of type Q, or `get`-able with the Point functor), or -1.
template<class Corners, class Point>
int PieceOf(const PieceCap &cap, const Corners &corners, const Point &point) {
  for (size_t p = 0; p < cap.pieces.size(); p++) {
    bool in = true;
    for (const auto &c : corners) {
      const VecQ v = point(c);
      if (!InPiece(cap.pieces[p], v[0], v[1], v[2])) { in = false; break; }
    }
    if (in) return (int)p;
  }
  return -1;
}

inline std::vector<PieceCap> ReadPieceCaps(const std::string &file) {
  std::ifstream in(file);
  CHECK(in.good()) << file;
  std::vector<PieceCap> caps;
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string word;
    if (!(ss >> word) || word[0] == '#') continue;
    if (word == "cap") {
      std::string r;
      CHECK(ss >> r) << line;
      PieceCap c;
      c.wmax2 = Q(std::string_view(r));
      c.wmax2_d = c.wmax2.ToDouble();
      caps.push_back(std::move(c));
    } else {
      CHECK(word == "piece" && !caps.empty()) << line;
      Piece p;
      std::array<std::string, 3> t;
      while (ss >> t[0]) {
        CHECK(ss >> t[1] >> t[2]) << line;
        VecQ n{Q(std::string_view(t[0])), Q(std::string_view(t[1])), Q(std::string_view(t[2]))};
        p.normals_d.push_back({n[0].ToDouble(), n[1].ToDouble(), n[2].ToDouble()});
        p.normals.push_back(std::move(n));
      }
      CHECK(!p.normals.empty()) << line;
      caps.back().pieces.push_back(std::move(p));
    }
  }
  return caps;
}

}  // namespace piececap

#endif
