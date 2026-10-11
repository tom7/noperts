
#ifndef _NOPERT_MODEL_H
#define _NOPERT_MODEL_H

#include <array>

#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "yocto-math.h"
#include "model_vertices.h"

// The polyhedron the proof is about, as the exact rational model the
// certificates use.
//
// The C5 solids (the icosahedral ones and #231) have rotational symmetry of
// order 5 about z: vertex S k + s is seed s rotated by 2 pi k / 5 (S seeds).
// Those rotations have irrational entries (cos 72 = (sqrt 5 - 1)/4), so the
// certificates are checked against a fixed rational model instead: every
// coordinate rounded to a multiple of 2^-52, with each non-triangular face
// snapped exactly planar. Lean proves the result for every polyhedron with
// the exact symmetry within 6e-16 of this model (an `IModel`, a `C5Model`),
// and the true solid is one of them. The Septopert's rational vertices are
// the solid itself (solid::kModelExact).
//
// codebdd generates the model from the solid's model file (e.g.
// septopert_model.txt; #231: nopert231_root.txt) into
//   model_vertices.h     (C++: the doubles and exact rationals below)
//   model_vertices.lean  (installed into the Lean model)
//   model_vertices.json
// VERTICES are the IEEE doubles nearest the exact rationals (VertexQ).

inline constexpr int NUM_VERTICES = NUM_VERTICES_MODEL;
inline constexpr const double (&VERTICES)[NUM_VERTICES][3] = VERTICES_MODEL;

inline constexpr yocto::vec<double, 3> Vertex(size_t v) {
  return yocto::vec<double, 3>{
    VERTICES[v][0],
    VERTICES[v][1],
    VERTICES[v][2],
  };
}

// The exact rational vertices, as coordinate arrays (singleton).
const std::array<std::array<BigRat, 3>, NUM_VERTICES> &GetVerticesQ();

const BigVecQ3 &VertexQ(size_t v);

#endif
