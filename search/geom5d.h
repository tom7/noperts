// Geometry of the 5D search: view triangles (the outer view direction) and
// Cayley boxes (the relative rotation in one of four charts), in exact
// rationals (what the Lean rows record) and doubles (what the search
// evaluates with). Subdivisions match Lean exactly:
//
//   view split   SnubCube.ProjectiveView.split (children: three corners, then
//                the central triangle)
//   box split    AtlasInterval.lowerHalf / upperHalf (halve one coordinate at
//                its exact midpoint)
//   root boxes   AtlasFundamentalPrune.restrictedRootInterval
//   rotation     chartMatrix * cayleyMatrix (AtlasQuadratic, CayleyEdgeCertificate)
//
// All functions are pure.

#ifndef _NOPERT_GEOM5D_H
#define _NOPERT_GEOM5D_H

#include <array>
#include <string_view>
#include <utility>

#include "exact5d.h"
#include "yocto-math.h"

namespace geom5d {

using vec3 = yocto::vec<double, 3>;
using mat3 = yocto::mat<double, 3>;
using exact5d::Interval5;
using exact5d::Q;
using exact5d::TriangleQ;
using exact5d::VecQ;

// View triangles.
TriangleQ SplitTriangle(const TriangleQ &t, int child);
// Applies the subdivision digits ('0'..'3') in order.
TriangleQ SplitTrianglePath(TriangleQ t, std::string_view path);

// Projective roots (Lean AtlasProjectiveView.rootSign, binary order): root r
// has signs s_c = -1 iff bit (2 - c) of r is set; its triangle lies on the
// plane sum_c s_c u_c = 1 with s_c u_c >= 0 (Lean SignedTriangleValid).
int RootSign(int root, int c);
bool SignedTriangleValid(int root, const TriangleQ &t);
// The first root r with SignedTriangleValid(r, t), or -1. (Unique for a
// nondegenerate triangle unless all corners share a zero coordinate.)
int TriangleRoot(const TriangleQ &t);

// Whether every corner of `inner` is in the closed triangle `outer` (all on
// one root plane), i.e. Lean's InTriangle(inner) ⊆ InTriangle(outer).
bool TriangleContains(const TriangleQ &outer, const TriangleQ &inner);
// A triangle on t's root plane, SignedTriangleValid for that root,
// containing t, whose coordinates are dyadic with about `rel_bits` bits
// below t's size: t enlarged about its centroid by a relative
// 2^-(rel_bits - 4), corners rounded to the grid; t itself if there is none
// (e.g. t touches its root's boundary). Checking a certificate over it is
// much cheaper than over t, whose coordinates come from facet-plane
// intersections (~1000 bits).
TriangleQ OuterDyadicTriangle(const TriangleQ &t, int rel_bits = 30);

struct TriangleD {
  std::array<vec3, 3> corners;
};
TriangleD ToDouble(const TriangleQ &t);
TriangleD SplitTriangle(const TriangleD &t, int child);
vec3 Centroid(const TriangleD &t);
// Max chord between the normalized corners.
double AngularDiameter(const TriangleD &t);

// Cayley boxes over (x, y, z), closed.
struct BoxQ {
  std::array<Q, 3> lo, hi;
};
BoxQ RootBox(int chart);
// The lower or upper half along axis (0..2 = x, y, z).
BoxQ LowerHalf(const BoxQ &b, int axis);
BoxQ UpperHalf(const BoxQ &b, int axis);
// The cut point lo + (hi - lo) * eighths / 8 along axis (eighths in 1..7),
// and the parts below and above it (AtlasInterval.lowerAt / upperAt; the
// point is inside the range, so Lean's clamp does nothing).
Q CutPoint(const BoxQ &b, int axis, int eighths);
BoxQ LowerAt(const BoxQ &b, int axis, int eighths);
BoxQ UpperAt(const BoxQ &b, int axis, int eighths);
// The pose interval Lean rows carry: θ, φ at their fixed root range.
Interval5 ToInterval(const BoxQ &b);

struct BoxD {
  vec3 center, radius;
};
BoxD ToDouble(const BoxQ &b);
int WidestAxis(const BoxD &b);
bool ContainsOrigin(const BoxD &b);

// Rotations. Lean's pose has inner rotation = outer * chart * cayley(w); the
// search works with the relative rotation chart * cayley(w).
mat3 ChartMatrix(int chart);
mat3 CayleyMatrix(const vec3 &w);
mat3 RelativeRotation(int chart, const vec3 &w);

}  // namespace geom5d

#endif
