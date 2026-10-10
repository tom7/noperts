
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
// The polyhedron has rotational symmetry of order 5 about z (for the snub
// dodecahedron, a 5-fold axis of its icosahedral group): vertex 12k + s is
// seed s rotated by 2 pi k / 5. Those rotations have irrational entries
// (cos 72 = (sqrt 5 - 1)/4), so the certificates are checked against a fixed
// rational model instead: every coordinate rounded to a multiple of 2^-52,
// with each non-triangular face snapped exactly planar. Lean proves the
// result for every polyhedron with the exact symmetry within 6e-16 of this
// model (an `IModel`), and the true solid is one of them.
//
// codebdd generates the model from the model file (snub_model.txt) into
//   model_vertices.h     (C++: the doubles and exact rationals below)
//   model_vertices.lean  (installed into Noperthedron's Vertices.lean)
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
