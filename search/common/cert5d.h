// Certificate search for 5D leaves (double precision), producing candidates
// for Lean's projectiveGlobal rows (one contact triple; mixtures of up to
// four triples come later). A candidate is only accepted after
// exact5d::Valid confirms it on the exact box, so what the search writes is
// what Lean accepts.

#ifndef _NOPERT_CERT5D_H
#define _NOPERT_CERT5D_H

#include <array>
#include <vector>

#include "bounds5d.h"
#include "contacts5d.h"
#include "exact5d.h"
#include "geom5d.h"

namespace cert5d {

using vec3 = geom5d::vec3;

// The inner vertex used for each contact of the pool: the one sticking out
// furthest past the contact's support line at the box center and the
// triangle's centroid view (g_blend5d = 0). With g_blend5d = 2: box-aware,
// the candidate (of the three best vertices at the center and their blends,
// bounds5d::BlendCode) with the best Bernstein lower bound over the box at
// the centroid view. With g_blend5d = 4 (escalate, search5d's default),
// BestSingle and BestMixture try level 0 first and level 2 only where it
// fails, and then only on the triples whose inner choice it changes.
extern int g_blend5d;
std::vector<int> BestInner(const contacts5d::ContactPool &pool, const geom5d::TriangleD &tri,
                           const geom5d::BoxD &box, int chart);

// Double mirror of Lean's bernsteinDisplacementLower for one triple with the
// given inner vertices and ball multiplier.
double DisplacementLower(const contacts5d::ContactPool &pool, const contacts5d::Triple &triple,
                         const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
                         const geom5d::BoxD &box, int chart, double ball_multiplier = 0.0);

// DisplacementLower - dBound * weightedDefectUpper - displacementError
// (Lean's displacement obligation, in double; positive = expected to pass).
double Margin(const contacts5d::ContactPool &pool, const contacts5d::Triple &triple,
              const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
              const geom5d::BoxD &box, int chart, double ball_multiplier = 0.0);

struct Single {
  int triple = -1;
  std::array<int, 3> inner{};
  double margin = -1e300;
};

// The best single triple by Margin, after screening all triples at the box
// center and centroid view and fully evaluating the top `max_full` of them.
Single BestSingle(const contacts5d::ContactPool &pool, const geom5d::TriangleD &tri,
                  const geom5d::BoxD &box, int chart, int max_full = 64);

// The exact Lean box for a single-triple candidate.
// (root: the view triangle's projective root, Lean's Box.root.)
exact5d::GlobalBox ExactGlobalBox(const contacts5d::ContactPool &pool, const Single &s,
                                  const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                                  int chart, int root);

// Mixtures (Lean's projectiveMixedGlobal): a convex combination of up to four
// triples' view-control quadratics. Its Bernstein coefficients are the same
// combination of each component's, so the best weights solve
//   max_w min_r sum_k w_k a[k][r],  a[k] = MixtureColumn(component k).
struct Mixture {
  std::vector<int> triples;
  std::vector<std::array<int, 3>> inner;
  std::vector<double> w;
  double margin = -1e300;  // max-min value minus displacementError
};

// The 6 x 27 Bernstein coefficients of a component's distinct view controls
// (corners, then the 01, 02, 12 off-diagonal controls), minus
// dBound * weightedDefectUpper.
std::vector<double> MixtureColumn(const contacts5d::ContactPool &pool,
                                  const contacts5d::Triple &triple,
                                  const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
                                  const geom5d::BoxD &box, int chart);

// Greedy column generation: start from the best single triple; repeatedly
// add the screened candidate that best raises the current bottleneck
// coefficient, re-solving the weights, up to max_components.
Mixture BestMixture(const contacts5d::ContactPool &pool, const geom5d::TriangleD &tri,
                    const geom5d::BoxD &box, int chart, int max_components = 4,
                    int candidates = 128);

// Exact weights for Lean: each rounded down to a multiple of 2^-40, the last
// taking the remainder (so they are nonnegative and sum to exactly 1).
std::vector<BigRat> RationalWeights(const std::vector<double> &w);

// The exact Lean mixed box (padded to four components with zero weight).
exact5d::MixedBox ExactMixedBox(const contacts5d::ContactPool &pool,
                                const std::vector<int> &triples,
                                const std::vector<std::array<int, 3>> &inner,
                                const std::vector<BigRat> &weights,
                                const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                                int chart, int root);

}  // namespace cert5d

#endif
