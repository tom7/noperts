// The snub dodecahedron's settings for the shared search code
// (../common): its model headers and what its search uses.
#ifndef _NOPERT_SOLID_H
#define _NOPERT_SOLID_H

#include "matrix_table.h"
#include "model_vertices.h"
#include "symmetry_neighbors.h"

namespace solid {

// The rational vertices are a rounding of the solid (within 6e-16), so the
// certificates carry the model error terms.
inline constexpr bool kModelExact = false;

// The 5D search's charts are 0..kMaxChart (chart 3 is a fixed table in
// Lean); the fivefold symmetry narrows the root box and gives the
// fundamental prune (pf).
inline constexpr int kMaxChart = 2;
inline constexpr bool kFivefold = true;

// The icosahedral prune (pi): the rotations by +-72 degrees about the six
// 5-fold axes, rounded to 10^-12.
inline constexpr MatrixTable kSymmetryNeighbors{NUM_SYMMETRY_NEIGHBORS, SYMMETRY_NEIGHBOR_DENOM, false,
                                                SYMMETRY_NEIGHBOR_NUM};
// No half-turn prune (the solid is not centrally symmetric) and no tie leaves.
inline constexpr MatrixTable kHalfTurnGroup{};
inline constexpr MatrixTable kTieHalfTurns{};

// No bridge contacts (contacts5d::PoolParams::bridge_ratio's default).
inline constexpr double kBridgeRatio = 0;

// The view triangle is in root 0; geom5d::OuterDyadicTriangle does not check
// that the enlarged triangle stays in the octant (the certificates over one
// that leaves it fail, and are kept over the exact triangle).
inline constexpr bool kOuterTriangleInRoot = false;

// codebdd's default --model_file.
inline constexpr const char *kModelFile = "snub_model.txt";

}  // namespace solid

#endif
