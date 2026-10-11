// Candidate contacts and contact triples for the 5D search's certificates.
//
// A contact is one outer silhouette edge direction with a support vertex,
// exactly as Lean's AxisCertificate records it: the edge direction is
//   e = (mix/1000) (v[edge_start] - v[edge_finish])
//       + (1 - mix/1000) (v[edge_start2] - v[edge_finish2]),
// and `vertex` is the outer vertex whose support line it is. The double
// `edge` here is computed from those same integers, so the search and the
// exact checker (exact5d) evaluate the same contact.
//
// A pool is the deterministic function of (view triangle, PoolParams) below;
// certificate rows index triples by position in it and record the params, so
// the pool can be rebuilt exactly when packing.

#ifndef _NOPERT_CONTACTS5D_H
#define _NOPERT_CONTACTS5D_H

#include <array>
#include <utility>
#include <vector>

#include "exact5d.h"
#include "geom5d.h"
#include "solid.h"

namespace contacts5d {

using vec3 = geom5d::vec3;

struct Contact {
  int vertex = 0;
  int edge_start = 0, edge_finish = 0, edge_start2 = 0, edge_finish2 = 0;
  int mix = 1000;  // 0..1000
  vec3 edge = {0, 0, 0};
  // Max over the triangle's corners of the largest support excess of any
  // other vertex past this contact's support line (>= 0; 0 for a true
  // silhouette support over the whole triangle).
  double defect = 0.0;
};

struct Triple {
  // Contact indices, ordered so that the three contact weights are positive
  // over the triangle (Lean's orientation).
  std::array<int, 3> c{};
  // Double-precision bound on Lean's weightedDefectUpper (with margin).
  double weighted_defect_upper = 0.0;
};

struct PoolParams {
  // Edge directions sampled per silhouette corner: mix values
  // round(1000 s / (cone_samples + 1)), s = 0 .. cone_samples + 1.
  int cone_samples = 8;
  // Off-silhouette contacts (at vertices not on the centroid view's hull,
  // along real polyhedron edges) are kept if their defect is at most this.
  double off_silhouette_max_defect = 0.002;
  // Bridge contacts across silhouette edges shorter than bridge_ratio times
  // the longest (0: none; the default is the solid's), kept if their defect is
  // at most bridge_max_defect.
  // Part of the pool definition (journals index triples in it).
  double bridge_ratio = solid::kBridgeRatio;
  double bridge_max_defect = 0.01;
  // Triples are indexed by 8 bits on the GPU.
  int max_contacts = 256;
};

struct ContactPool {
  PoolParams params;
  std::vector<Contact> contacts;
  std::vector<Triple> triples;
};

ContactPool BuildContactPool(const geom5d::TriangleD &tri, const PoolParams &params);

// The polyhedron's edges (i < j): pairs of vertices that lie on two common
// facet planes, computed exactly from the rational vertices.
const std::vector<std::pair<int, int>> &PolyhedronEdges();

// Silhouette (2D hull) of the vertices projected along `view`, as a vertex
// cycle in the orientation the contacts use.
std::vector<int> SilhouetteCycle(const vec3 &view);

// Lean's AxisCertificate for a triple of the pool, with the nonzero witness
// for each contact chosen as the vertex of most negative exact support bound
// over `tri`. B is not used by the 5D checks; it is set to 1.
exact5d::AxisCertificate ToAxisCertificate(const ContactPool &pool, const Triple &triple,
                                           const exact5d::TriangleQ &tri);

}  // namespace contacts5d

#endif
