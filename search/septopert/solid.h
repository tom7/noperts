// The Septopert's settings for the shared search code (../common): its model
// headers and what its search uses.
#ifndef _NOPERT_SOLID_H
#define _NOPERT_SOLID_H

#include "matrix-table.h"
#include "mirror-q.h"
#include "model-vertices.h"
#include "symmetry-neighbors.h"

namespace solid {

// The rational vertices are the solid itself (MODEL_EXACT: codebdd writes it
// for a model without C5 seeds), so the certificates have no model error
// terms and exact support ties are allowed.
inline constexpr bool kModelExact = MODEL_EXACT;

// The 5D search's charts are 0..kMaxChart, each over the whole Cayley cube:
// no fivefold narrowing of the root box and no fundamental prune (pf).
inline constexpr int kMaxChart = 3;
inline constexpr bool kFivefold = false;

// The C3 cell prune (pi): the C3 rotations, exact.
inline constexpr MatrixTable kSymmetryNeighbors{NUM_SYMMETRY_NEIGHBORS, SYMMETRY_NEIGHBOR_DENOM,
                                                SYMMETRY_NEIGHBOR_EXACT, SYMMETRY_NEIGHBOR_NUM};
// The mirror prune (ph, the half-turn prune's leaf): the mirror-tie
// rotations Q_g, exact.
inline constexpr MatrixTable kHalfTurnGroup{MIRROR_Q_SIZE, MIRROR_Q_DENOM, MIRROR_Q_EXACT, MIRROR_Q_NUM};
// No tie leaves.
inline constexpr MatrixTable kTieHalfTurns{};

// The default of contacts5d::PoolParams::bridge_ratio (part of the pool
// definition): bridge contacts across short silhouette edges.
inline constexpr double kBridgeRatio = 0.1;

// The view domain spans two projective roots: geom5d::OuterDyadicTriangle
// keeps the enlarged triangle in its root's octant.
inline constexpr bool kOuterTriangleInRoot = true;

// geom5d::OuterDyadicTriangle measures the triangle by exact differences of
// its corners (#231's search used their doubles).
inline constexpr bool kTriangleSizeInDouble = false;

// codebdd's default --model_file.
inline constexpr const char *kModelFile = "septopert-model.txt";

}  // namespace solid

#endif
