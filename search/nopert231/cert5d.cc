#include "cert5d.h"

#include <algorithm>
#include <cmath>
#include <utility>
#include <vector>

#include "base/logging.h"
#include "nopert231.h"

namespace cert5d {

using bounds5d::Quad;
using contacts5d::ContactPool;
using contacts5d::Triple;

namespace {

std::array<vec3, 3> WeightCoefficients(const ContactPool &pool, const Triple &t) {
  const vec3 &e0 = pool.contacts[t.c[0]].edge;
  const vec3 &e1 = pool.contacts[t.c[1]].edge;
  const vec3 &e2 = pool.contacts[t.c[2]].edge;
  return {yocto::cross(e1, e2), yocto::cross(e2, e0), yocto::cross(e0, e1)};
}

// Lean's adjustedViewDisplacementQuadratic at view n.
Quad ViewDisplacement(const ContactPool &pool, const Triple &t,
                      const std::array<std::array<Quad, 3>, 3> &d, const vec3 &n,
                      double ball_multiplier) {
  const auto w = WeightCoefficients(pool, t);
  Quad q;
  for (int i = 0; i < 3; i++) {
    q = bounds5d::Add(q, bounds5d::Scale(yocto::dot(n, w[i]),
                                         bounds5d::ContactTerm(d[i], n, pool.contacts[t.c[i]].edge)));
  }
  if (ball_multiplier != 0.0) {
    Quad constraint;
    constraint.c = {-3, 0, 0, 0, 1, 0, 0, 1, 0, 1};
    q = bounds5d::Add(q, bounds5d::Scale(ball_multiplier, constraint));
  }
  return q;
}

}  // namespace

std::vector<int> BestInner(const ContactPool &pool, const geom5d::TriangleD &tri,
                           const geom5d::BoxD &box, int chart) {
  const vec3 view = geom5d::Centroid(tri);
  std::vector<int> best(pool.contacts.size(), 0);
  for (size_t c = 0; c < pool.contacts.size(); c++) {
    const auto &ct = pool.contacts[c];
    double best_v = -1e300;
    for (int k = 0; k < NUM_VERTICES; k++) {
      const auto d = bounds5d::Displacement(chart, k, ct.vertex);
      const double v = bounds5d::Eval(bounds5d::ContactTerm(d, view, ct.edge), box.center);
      if (v > best_v) {
        best_v = v;
        best[c] = k;
      }
    }
  }
  return best;
}

double DisplacementLower(const ContactPool &pool, const Triple &triple,
                         const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
                         const geom5d::BoxD &box, int chart, double ball_multiplier) {
  std::array<std::array<Quad, 3>, 3> d;
  for (int i = 0; i < 3; i++) {
    d[i] = bounds5d::Displacement(chart, inner[i], pool.contacts[triple.c[i]].vertex);
  }
  std::array<Quad, 3> at_corner;
  for (int i = 0; i < 3; i++) {
    at_corner[i] = ViewDisplacement(pool, triple, d, tri.corners[i], ball_multiplier);
  }
  double lower = 1e300;
  for (int i = 0; i < 3; i++) {
    lower = std::min(lower, bounds5d::BernsteinLower(at_corner[i], box));
    for (int j = i + 1; j < 3; j++) {
      const vec3 mid = (tri.corners[i] + tri.corners[j]) * 0.5;
      // Off-diagonal control: 2 Q(mid) - (Q(t_i) + Q(t_j)) / 2.
      const Quad control = bounds5d::Add(
          bounds5d::Scale(2.0, ViewDisplacement(pool, triple, d, mid, ball_multiplier)),
          bounds5d::Scale(-0.5, bounds5d::Add(at_corner[i], at_corner[j])));
      lower = std::min(lower, bounds5d::BernsteinLower(control, box));
    }
  }
  return lower;
}

double Margin(const ContactPool &pool, const Triple &triple, const std::array<int, 3> &inner,
              const geom5d::TriangleD &tri, const geom5d::BoxD &box, int chart,
              double ball_multiplier) {
  return DisplacementLower(pool, triple, inner, tri, box, chart, ball_multiplier) -
         bounds5d::DBound(box) * triple.weighted_defect_upper -
         bounds5d::DisplacementError(box);
}

Single BestSingle(const ContactPool &pool, const geom5d::TriangleD &tri,
                  const geom5d::BoxD &box, int chart, int max_full) {
  Single best;
  if (pool.triples.empty()) return best;
  const std::vector<int> inner_of = BestInner(pool, tri, box, chart);

  // Screen: the displacement at the box center and centroid view, minus the
  // defect charge.
  const vec3 view = geom5d::Centroid(tri);
  std::vector<double> term(pool.contacts.size());
  for (size_t c = 0; c < pool.contacts.size(); c++) {
    const auto &ct = pool.contacts[c];
    term[c] = bounds5d::Eval(
        bounds5d::ContactTerm(bounds5d::Displacement(chart, inner_of[c], ct.vertex), view, ct.edge),
        box.center);
  }
  const double dbound = bounds5d::DBound(box);
  std::vector<std::pair<double, int>> screened;
  screened.reserve(pool.triples.size());
  for (size_t t = 0; t < pool.triples.size(); t++) {
    const Triple &tr = pool.triples[t];
    const auto w = WeightCoefficients(pool, tr);
    double v = 0.0;
    for (int i = 0; i < 3; i++) v += yocto::dot(view, w[i]) * term[tr.c[i]];
    screened.push_back({v - dbound * tr.weighted_defect_upper, (int)t});
  }
  const int full = std::min<int>(max_full, screened.size());
  std::partial_sort(screened.begin(), screened.begin() + full, screened.end(),
                    [](const auto &a, const auto &b) { return a.first > b.first; });
  for (int f = 0; f < full; f++) {
    const int t = screened[f].second;
    const Triple &tr = pool.triples[t];
    const std::array<int, 3> inner = {inner_of[tr.c[0]], inner_of[tr.c[1]], inner_of[tr.c[2]]};
    const double m = Margin(pool, tr, inner, tri, box, chart);
    if (m > best.margin) best = Single{.triple = t, .inner = inner, .margin = m};
  }
  return best;
}

exact5d::GlobalBox ExactGlobalBox(const ContactPool &pool, const Single &s,
                                  const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                                  int chart) {
  CHECK(s.triple >= 0);
  exact5d::GlobalBox g;
  g.interval = geom5d::ToInterval(box);
  g.triangle = tri;
  g.chart = chart;
  g.certificate = contacts5d::ToAxisCertificate(pool, pool.triples[s.triple], tri);
  g.inner_index = s.inner;
  g.ball_multiplier = exact5d::Q(0);
  return g;
}

}  // namespace cert5d
