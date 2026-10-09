// The nontrivial rotations of K's C3 (nopert_233, axis (1,1,1); Noperthedron's
// Nopert7.c3Mat 1 and c3Mat 2: the cyclic coordinate permutations), exact
// (denominator 1, no rounding allowance). The C3 cell prune
// (exact5d::IcoPruneValid) removes boxes where trace(R c_k) > trace(R) for
// k = n + 1 (Lean: Nopert7.InC3vCell).
#ifndef _NOPERT_SYMMETRY_NEIGHBORS_H
#define _NOPERT_SYMMETRY_NEIGHBORS_H

#include <cstdint>

inline constexpr int NUM_SYMMETRY_NEIGHBORS = 2;
inline constexpr int64_t SYMMETRY_NEIGHBOR_DENOM = 1;
// The entries are exact: the prune needs a strictly positive lower bound.
inline constexpr bool SYMMETRY_NEIGHBOR_EXACT = true;
// Row-major numerators: c3Mat 1 = (x,y,z) -> (y,z,x), c3Mat 2 = its square.
inline constexpr int64_t SYMMETRY_NEIGHBOR_NUM[NUM_SYMMETRY_NEIGHBORS][9] = {
  {0, 1, 0, 0, 0, 1, 1, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 1, 0},
};

#endif
