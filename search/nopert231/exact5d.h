// Exact rational checks for the 5D search's certificate leaves, ported 1:1
// from the Lean definitions that decide them:
//
//   projectiveGlobal       Noperthedron/Nopert229/AtlasProjectiveGlobalCertificate.lean
//   projectiveMixedGlobal  Noperthedron/Nopert229/AtlasProjectiveMixedGlobalCertificate.lean
//
// Lean is the specification. Each function here carries the name of the Lean
// definition it mirrors, and exact5d_test checks agreement with Lean on
// generated boxes (via the exact5d_golden Lean executable). Use this both in
// the search (to pre-check a leaf before writing it) and in packing, so that
// what C++ accepts is exactly what Lean accepts.
//
// Only view root 0 (the upper fivefold view, all signs +) is supported; that
// is the only root the 5D search uses.

#ifndef _NOPERT229_EXACT5D_H
#define _NOPERT229_EXACT5D_H

#include <array>

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

}  // namespace exact5d

#endif
