// Exact rational checks for the 5D search's certificate leaves, ported 1:1
// from the Lean definitions that decide them:
//
//   projectiveGlobal       Noperthedron/PentagonalHexecontahedron/AtlasProjectiveGlobalCertificate.lean
//   projectiveMixedGlobal  Noperthedron/PentagonalHexecontahedron/AtlasProjectiveMixedGlobalCertificate.lean
//
// Lean is the specification. Each function here carries the name of the Lean
// definition it mirrors, and exact5d_test checks agreement with Lean on
// generated boxes (via the exact5d_golden Lean executable). Use this both in
// the search (to pre-check a leaf before writing it) and in packing, so that
// what C++ accepts is exactly what Lean accepts.
//
// Only view root 0 (Lean's rootSign 0 = (+1, +1, +1), the positive octant,
// which contains the model's view triangle) is supported; that is the only
// root the 5D search uses.

#ifndef _NOPERT_EXACT5D_H
#define _NOPERT_EXACT5D_H

#include <array>
#include <vector>

#include "bignum/big.h"

namespace exact5d {

using Q = BigRat;
using VecQ = std::array<Q, 3>;
// Three projective corners (each on the plane u0 + u1 + u2 = 1 for root 0).
using TriangleQ = std::array<VecQ, 3>;

// Checker.RatBall: the set [center - radius, center + radius].
struct RatBall {
  Q center{0};
  Q radius{0};
};

RatBall BallConst(const Q &q);
RatBall BallAdd(const RatBall &a, const RatBall &b);
RatBall BallNeg(const RatBall &a);
RatBall BallSub(const RatBall &a, const RatBall &b);
RatBall BallMul(const RatBall &a, const RatBall &b);
RatBall BallOfEndpoints(const Q &lo, const Q &hi);

// Checker.RatQuadratic3: c0 + cx x + cy y + cz z + cxx x² + cxy xy + cxz xz
// + cyy y² + cyz yz + czz z².
struct Quad3 {
  Q c0{0}, cx{0}, cy{0}, cz{0}, cxx{0}, cxy{0}, cxz{0}, cyy{0}, cyz{0}, czz{0};
};

Quad3 QuadAdd(const Quad3 &a, const Quad3 &b);
Quad3 QuadSub(const Quad3 &a, const Quad3 &b);
Quad3 QuadScale(const Q &s, const Quad3 &a);
Q QuadEvalQ(const Quad3 &q, const Q &x, const Q &y, const Q &z);
// RatQuadratic3.evalBall (centered, cancellation-preserving).
RatBall QuadEvalBall(const std::array<RatBall, 3> &vars, const Quad3 &q);
// QuadraticBernstein.lower: min of the (2,2,2) tensor Bernstein coefficients
// of q on the box given by vars.
Q BernsteinLower(const std::array<RatBall, 3> &vars, const Quad3 &q);

// AtlasProjectiveLocalCertificate.AxisCertificate.
struct AxisCertificate {
  std::array<int, 3> edge_start{}, edge_finish{}, edge_start2{}, edge_finish2{};
  // Convex mixing weight mix / 1000, in 0..1000.
  std::array<int, 3> mix{};
  // Selected outer support vertex per contact (symmetry index 0).
  std::array<int, 3> index{};
  std::array<int, 3> nonzero_witness{};
  Q B{0};
};

// AtlasInterval over the pose (θ, φ, x, y, z); the checks below only use the
// Cayley coordinates x, y, z (indices 2..4).
struct Interval5 {
  std::array<Q, 5> min, max;
};

// AtlasProjectiveGlobalCertificate.Box (root fixed to 0).
struct GlobalBox {
  Interval5 interval;
  TriangleQ triangle;
  int chart = 0;
  AxisCertificate certificate;
  std::array<int, 3> inner_index{};
  Q ball_multiplier{0};
};

// AtlasProjectiveMixedGlobalCertificate.Component / Box.
struct MixedComponent {
  AxisCertificate certificate;
  std::array<int, 3> inner_index{};
  Q ball_multiplier{0};
};
struct MixedBox {
  Interval5 interval;
  TriangleQ triangle;
  int chart = 0;
  std::array<MixedComponent, 4> component;
  std::array<Q, 4> weight;
};

// The constants of the Lean checker.
Q TightVertexErrorQ();  // 6 / 10^16
Q SupportError();       // 10 * tightVertexErrorQ

// Per-box quantities (names follow the Lean Box.* definitions).
VecQ EdgeQ(const AxisCertificate &cert, int i);
VecQ WeightCoefficient(const AxisCertificate &cert, int i);
Q SupportAt(const GlobalBox &box, int corner, int i, int k);
Q SupportUpper(const GlobalBox &box, int i, int k);
// SupportUpper(box, i, k) for every contact i and vertex k, sharing one
// precomputation (row i has NUM_VERTICES entries).
std::array<std::vector<Q>, 3> SupportUppers(const GlobalBox &box);
Q WeightAt(const GlobalBox &box, int corner, int i);
Q WeightLower(const GlobalBox &box, int i);
Q WeightUpper(const GlobalBox &box, int i);
Q WeightedDefectUpper(const GlobalBox &box);
Quad3 ContactQuadratic(const GlobalBox &box, int i, int c);
Quad3 ViewControlQuadratic(const GlobalBox &box, int i, int j);
Q BernsteinDisplacementLower(const GlobalBox &box);
RatBall AdjustedDisplacementBall(const GlobalBox &box);
Q CertifiedDisplacementLower(const GlobalBox &box);
Q DBound(const GlobalBox &box);
Q DisplacementError(const GlobalBox &box);

// Box.Admissible and Box.Valid.
bool Admissible(const GlobalBox &box);
bool Valid(const GlobalBox &box);
// Slack of the displacement obligation:
// certifiedDisplacementLower - dBound * weightedDefectUpper - displacementError.
// Valid iff Admissible and slack >= 0.
Q DisplacementSlack(const GlobalBox &box);

GlobalBox ComponentBox(const MixedBox &box, int k);
Q BernsteinDisplacementLower(const MixedBox &box);
Q WeightedDefectUpper(const MixedBox &box);
bool Valid(const MixedBox &box);
Q DisplacementSlack(const MixedBox &box);

// Leaves that need no certificate data beyond the pose box.

// RatQuadratic3.evalTightBall (keeps the nonnegativity of the centered
// diagonal squares).
RatBall QuadEvalTightBall(const std::array<RatBall, 3> &vars, const Quad3 &q);
// RationalApprox.sqrtQUp16: an upper bound on sqrt(x) that is a multiple of
// 10^-16 (0 for x <= 0).
Q SqrtQUp16(const Q &x);

// radiusPrune: AtlasProjectiveSolutionTree.Interval.outsideCayleyBall.
bool OutsideCayleyBall(const Interval5 &iv);

// fundamentalPrune: AtlasFundamentalPrune.Box.Valid. direction is +1
// (Direction.positive) or -1 (Direction.negative).
Q FundamentalLower(const Interval5 &iv, int chart, int direction);
bool FundamentalPruneValid(const Interval5 &iv, int chart, int direction);
// Icosahedral prune (icosahedral solids): some right symmetry, the rotation
// by +-72 degrees about one of the six 5-fold axes (neighbor n of
// symmetry_neighbors.h), strictly increases trace over the whole box, so the
// box is outside the identity's icosahedral Dirichlet cell.
Q IcoPruneLower(const Interval5 &iv, int chart, int n);
// Half-turn prune (centrally symmetric icosahedral solids, e.g. the deltoidal
// hexecontahedron): a pose (u, R) is a passage iff (u, H_u R g) is, for H_u
// the half-turn about the view u and g in I (pi_u(H_u X) = -pi_u(X), K = -K,
// gK = K). So R may be taken to maximize the trace over {R g, H_u R g}, and a
// box is pruned when trace(H_u R g) > trace(R) over all of it for one g
// (index into ico_group.h). With u = p / |p|, p = sum_c lambda_c P_c over
// the view triangle's corners, (trace(H_p R G) - trace(R)) |p|^2 D(w) is a
// homogeneous quadratic in lambda with degree-2 Bernstein coefficients
// b_cd(w), quadratic in the Cayley coordinates w:
//   b_cd = sum_ik N_ik [P_c,i (G P_d)_k + P_d,i (G P_c)_k - (P_c.P_d)(G_ki + delta_ik)],
// N = S Num(w) the Cayley numerator in the chart. The prune holds when every
// b_cd exceeds its rounding allowance on the box.
Q HalfTurnPruneLower(const Interval5 &iv, const TriangleQ &tri, int chart, int g, int c, int d);
Q HalfTurnPruneAllowance(const TriangleQ &tri, int c, int d);
bool HalfTurnPruneValid(const Interval5 &iv, const TriangleQ &tri, int chart, int g);
// Tie leaf (deltoidal hexecontahedron): every pose of the box has
// trace(H_u R H_x) >= tau = (3 - rho^2) / (1 + rho^2), i.e. the Cayley vector
// of S = H_u R H_x has norm <= rho, which the tie tube (tietube.cc) of
// pinning normal n certifies for the view. Same Bernstein form as the
// half-turn prune, with G = H_x (tie_normals.h) and -tau (P_c.P_d) D(w) in
// place of -(P_c.P_d) trace(N).
Q TieLeafLower(const Interval5 &iv, const TriangleQ &tri, int chart, int n, const Q &rho, int c, int d);
bool TieLeafValid(const Interval5 &iv, const TriangleQ &tri, int chart, int n, const Q &rho);
bool IcoPruneValid(const Interval5 &iv, int chart, int n);

// symmetryTube: AtlasProjectiveLocalViewTree.Tube.Valid for chart 0 and
// symmetry index 0 (the identity tube), i.e. identityMismatchRadius <= r.
Q IdentityMismatchRadius(const Interval5 &iv);
bool IdentityTubeValid(const Interval5 &iv, const Q &r);

// AtlasFundamentalPrune.restrictedRootInterval: the root pose box of a chart.
Interval5 RestrictedRootInterval(int chart);

}  // namespace exact5d

#endif
