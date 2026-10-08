// The mirror-tie rotations of K (nopert_233, axis (1,1,1)): Q_i = -sigma_i for
// the mirror sigma_i = the transposition of the two coordinates other than i
// (Noperthedron's Nopert7.mirrorQMat i, the half-turn about the mirror's
// normal), exact (denominator 1, no rounding allowance). The mirror prune
// (exact5d::HalfTurnPruneValid) removes boxes where trace(H_u R Q_i) >
// trace(R) over the whole box and view triangle (Lean: Nopert7.InC3vCell).
#ifndef _NOPERT_MIRROR_Q_H
#define _NOPERT_MIRROR_Q_H

#include <cstdint>

inline constexpr int MIRROR_Q_SIZE = 3;
inline constexpr int64_t MIRROR_Q_DENOM = 1;
inline constexpr bool MIRROR_Q_EXACT = true;
// Row-major numerators.
inline constexpr int64_t MIRROR_Q_NUM[MIRROR_Q_SIZE][9] = {
  {-1, 0, 0, 0, 0, -1, 0, -1, 0},
  {0, 0, -1, 0, -1, 0, -1, 0, 0},
  {0, -1, 0, -1, 0, 0, 0, 0, -1},
};

#endif
