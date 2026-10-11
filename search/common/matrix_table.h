// A table of 3x3 matrices (int64 numerators over one denominator): a solid's
// symmetry neighbors, half-turn group or tie half-turns, which its solid.h
// takes from its generated model headers (symmetry_neighbors.h, ...).
#ifndef _NOPERT_MATRIX_TABLE_H
#define _NOPERT_MATRIX_TABLE_H

#include <cstdint>

struct MatrixTable {
  int size = 0;
  int64_t denom = 1;
  // Whether the entries are the exact matrices (no rounding allowance).
  bool exact = true;
  // size rows of row-major numerators (nullptr for an empty table).
  const int64_t (*num)[9] = nullptr;
};

#endif
