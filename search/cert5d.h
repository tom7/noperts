// Certificate search for 5D leaves (double precision), producing candidates
// for Lean's projectiveGlobal rows (one contact triple; mixtures of up to
// four triples come later). A candidate is only accepted after
// exact5d::Valid confirms it on the exact box, so what the search writes is
// what Lean accepts.

#ifndef _NOPERT229_CERT5D_H
#define _NOPERT229_CERT5D_H

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
// triangle's centroid view.
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
exact5d::GlobalBox ExactGlobalBox(const contacts5d::ContactPool &pool, const Single &s,
                                  const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                                  int chart);

}  // namespace cert5d

#endif
