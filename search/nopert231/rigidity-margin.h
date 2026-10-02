// First-order rigidity of the identity pose of a convex polyhedron (given
// by its vertices), and a search for near-identity Rupert passages.
//
// For an outer view direction u, rotate the inner copy by a small angle
// theta about a unit axis w (and translate it optimally in the view plane).
// To first order the best achievable clearance is -theta * f_u(w), where
//   f_u(w) = min_t max_j ( n_j . (P(w x v_j) + t) )
// over the silhouette constraints j = (hull vertex v_j, outward unit
// normal n_j of an adjacent hull edge). The margin m(u) = min_{|w|=1} f_u(w)
// is in length units per radian. If m(u) < 0, there is a near-identity
// Rupert passage at u (how #214 and #229 fail; nopert229/notes/Q.md 1.8).
// We minimize over the max-norm cube |w|_inf = 1 (six small LPs); this has
// the same sign as the Euclidean margin.
//
// "Robust" margin: the same, ignoring vertices on a silhouette edge (exterior
// angle below kMergeAngle), e.g. a quad's vertices when it is edge-on. It is
// the limit of the true margin from the side where they are eclipsed.

#ifndef _NOPERT229_RIGIDITY_MARGIN_H
#define _NOPERT229_RIGIDITY_MARGIN_H

#include <atomic>
#include <cstdint>
#include <limits>
#include <utility>
#include <vector>

#include "yocto-math.h"

namespace rigidity {

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

struct Margin {
  // min of f_u over the cube |w|_inf = 1 (same sign as the Euclidean
  // margin, within a factor of sqrt(3) of it).
  double m = -std::numeric_limits<double>::infinity();
  // f_u at the unit vector along the cube minimizer: an upper bound on the
  // Euclidean margin min_{|w|=1} f_u(w).
  double m_euclid_upper = -std::numeric_limits<double>::infinity();
  // Worst rotation axis (unit).
  vec3 axis{0, 0, 0};
};

// A silhouette constraint: the inner vertex's displacement along outward
// unit normal n (2D), whose rotation part is a . w (a = v x N in 3D).
struct Constraint { vec2 n; vec3 a; };
// The silhouette constraints at view u (robust: see above).
std::vector<Constraint> SilhouetteConstraints(const std::vector<vec3> &verts, vec3 u,
                                              bool robust);
// 2D cross product.
double Cross2(const vec2 &a, const vec2 &b);
// f_u(w) for the constraints of view u.
double EvalF(const std::vector<Constraint> &cons, const vec3 &w);
// min of f_u over the cube face w[coord] = sign: (value, minimizer w).
std::pair<double, vec3> MinOnCubeFace(const std::vector<Constraint> &cons, int coord, double sign);

Margin FirstOrderMargin(const std::vector<vec3> &verts, vec3 u, bool robust);
// How often FirstOrderMargin's face LP disagreed with a direct evaluation and
// a search was used instead (the LP is occasionally wrong on degenerate views).
extern std::atomic<int64_t> lp_fallbacks;

// Local minimization of the true margin over views near u0: (margin, view).
std::pair<double, vec3> RefineView(const std::vector<vec3> &verts, vec3 u0);

// Best clearance (max over translations, by an exact LP over outer hull
// edges) of the inner copy rotated by theta about axis, at outer view u.
// Positive means a Rupert passage. Computed in difference form, so that its
// absolute error scales with theta: near the identity, clearances of 1e-12
// are meaningful.
double PassageClearance(const std::vector<vec3> &verts, vec3 u, vec3 axis, double theta);

struct PassageResult { double clearance; vec3 u; vec3 axis; double theta; };
// Local search for a passage near view u0 and axis axis0, over theta in
// [1e-12, 1e-3], the axis and the view.
PassageResult SearchPassage(const std::vector<vec3> &verts, vec3 u0, vec3 axis0);
// The same at a fixed rotation angle theta (over the view and the axis).
// Where the first-order margin is ~0, SearchPassage drifts to theta -> 0
// (clearance -> 0-); this probes each scale of theta separately.
PassageResult SearchPassageAt(const std::vector<vec3> &verts, vec3 u0, vec3 axis0, double theta);

}  // namespace rigidity

#endif
