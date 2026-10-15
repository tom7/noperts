// The snub cube's settings for the shared search code (../common): its model
// headers and what its search uses.
#ifndef _NOPERT_SOLID_H
#define _NOPERT_SOLID_H

#include "matrix-table.h"
#include "model-vertices.h"
#include "symmetry-neighbors.h"

namespace solid {

// The rational vertices are the O-orbit of a rounded seed, within 1e-16 of
// the exact (irrational) solid, so the certificates carry the model error
// terms (codebdd's MODEL_EXACT, written for models without C5 seeds, does not
// apply).
inline constexpr bool kModelExact = false;

// The 5D search's charts are 0..kMaxChart, each over the whole Cayley cube
// (no fivefold narrowing and no fundamental prune): the O cell prune removes
// charts 1-3.
inline constexpr int kMaxChart = 3;
inline constexpr bool kFivefold = false;

// The O cell prune (pi): the 23 nontrivial rotations of O, exact.
inline constexpr MatrixTable kSymmetryNeighbors{NUM_SYMMETRY_NEIGHBORS, SYMMETRY_NEIGHBOR_DENOM,
                                                SYMMETRY_NEIGHBOR_EXACT, SYMMETRY_NEIGHBOR_NUM};
// No half-turn prune (the solid is not centrally symmetric and has no
// mirrors) and no tie leaves.
inline constexpr MatrixTable kHalfTurnGroup{};
inline constexpr MatrixTable kTieHalfTurns{};

// No bridge contacts (contacts5d::PoolParams::bridge_ratio's default).
inline constexpr double kBridgeRatio = 0;

// The view triangle is in root 0; geom5d::OuterDyadicTriangle does not check
// that the enlarged triangle stays in the octant.
inline constexpr bool kOuterTriangleInRoot = false;

// geom5d::OuterDyadicTriangle measures the triangle by exact differences of
// its corners.
inline constexpr bool kTriangleSizeInDouble = false;

// codebdd's default --model_file.
inline constexpr const char *kModelFile = "sc-model.txt";

}  // namespace solid

#endif
