// Candidate #231's settings for the shared search code (../common): its
// model headers and what its search uses. (Its codebdd.cc is its own.)
#ifndef _NOPERT_SOLID_H
#define _NOPERT_SOLID_H

#include "matrix-table.h"
#include "model-vertices.h"

namespace solid {

// The rational vertices are a rounding of the solid (within 6e-16), so the
// certificates carry the model error terms.
inline constexpr bool kModelExact = false;

// The 5D search's charts are 0..kMaxChart (chart 3 is a fixed table in
// Lean); the fivefold symmetry narrows the root box and gives the
// fundamental prune (pf).
inline constexpr int kMaxChart = 2;
inline constexpr bool kFivefold = true;

// No icosahedral prune (the symmetry is only C5), no half-turn prune and no
// tie leaves.
inline constexpr MatrixTable kSymmetryNeighbors{};
inline constexpr MatrixTable kHalfTurnGroup{};
inline constexpr MatrixTable kTieHalfTurns{};

// No bridge contacts (contacts5d::PoolParams::bridge_ratio's default).
inline constexpr double kBridgeRatio = 0;

// The view triangle is in root 0; geom5d::OuterDyadicTriangle does not check
// that the enlarged triangle stays in the octant (the certificates over one
// that leaves it fail, and are kept over the exact triangle).
inline constexpr bool kOuterTriangleInRoot = false;

// geom5d::OuterDyadicTriangle measures the triangle by the differences of
// its corners rounded to double (as #231's search did; the others take exact
// differences).
inline constexpr bool kTriangleSizeInDouble = true;

}  // namespace solid

#endif
