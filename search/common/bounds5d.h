// Double-precision mirror of the quadratic bounds in Lean's 5D leaf checks
// (see exact5d for the exact versions):
//
//   AtlasQuadratic.displacementQuadratic   d(w) = chart N(w) v_in - D(w) v_out
//   Box.viewDisplacementQuadratic          sum_i w_i(n) n.(e_i x d_i)
//   Box.viewControlQuadratic               Bernstein controls on the triangle
//   QuadraticBernstein.lower               (2,2,2) tensor Bernstein minimum
//
// Quadratics are over the Cayley coordinates (x, y, z), with coefficients
// in Lean's order c0, cx, cy, cz, cxx, cxy, cxz, cyy, cyz, czz.

#ifndef _NOPERT_BOUNDS5D_H
#define _NOPERT_BOUNDS5D_H

#include <array>

#include "geom5d.h"

namespace bounds5d {

using vec3 = geom5d::vec3;

struct Quad {
  std::array<double, 10> c{};
};

Quad Add(const Quad &a, const Quad &b);
Quad Scale(double s, const Quad &a);
double Eval(const Quad &q, const vec3 &w);

// Inner codes: k < NUM_VERTICES is vertex k; BlendCode(a, c, tn) (tn = 1..3)
// is the blended point (1 - tn/4) v_a + (tn/4) v_c, a point of the hull (an
// experiment: nopert229 SEPTOPERT-IMPROVEMENTS to-do 11; no Lean row yet).
int BlendCode(int a, int c, int tn);
bool DecodeBlend(int code, int *a, int *c, int *tn);

// The three components of the displacement of inner vertex (or blend code)
// `inner` from outer vertex `outer` (denominator cleared), as quadratics in w.
std::array<Quad, 3> Displacement(int chart, int inner, int outer);

// One contact's term n . (e x d(w)) = d(w) . (n x e), for view n.
Quad ContactTerm(const std::array<Quad, 3> &d, const vec3 &n, const vec3 &e);

// QuadraticBernstein.coefficient over the box, for (i, j, k) in 0..2 as
// index 9 i + 3 j + k; QuadraticBernstein.lower is their minimum.
std::array<double, 27> BernsteinCoefficients(const Quad &q, const geom5d::BoxD &box);
double BernsteinLower(const Quad &q, const geom5d::BoxD &box);

// AtlasEdgeCertificate.Box.dBound and displacementError.
double DBound(const geom5d::BoxD &box);
double DisplacementError(const geom5d::BoxD &box);

}  // namespace bounds5d

#endif
