#include "cert5d.h"

#include <algorithm>
#include <cmath>
#include <utility>
#include <vector>

#include "base/logging.h"
#include "bignum/big-overloads.h"
#include "lp5d.h"
#include "model.h"

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

namespace {
// The distinct view-control quadratics: corners 0, 1, 2, then the
// off-diagonal controls 2 Q(mid) - (Q(t_i) + Q(t_j)) / 2 for 01, 02, 12.
std::array<Quad, 6> ViewControls(const ContactPool &pool, const Triple &triple,
                                 const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
                                 int chart, double ball_multiplier) {
  std::array<std::array<Quad, 3>, 3> d;
  for (int i = 0; i < 3; i++) {
    d[i] = bounds5d::Displacement(chart, inner[i], pool.contacts[triple.c[i]].vertex);
  }
  std::array<Quad, 6> out;
  for (int i = 0; i < 3; i++) out[i] = ViewDisplacement(pool, triple, d, tri.corners[i], ball_multiplier);
  int n = 3;
  for (int i = 0; i < 3; i++) {
    for (int j = i + 1; j < 3; j++) {
      const vec3 mid = (tri.corners[i] + tri.corners[j]) * 0.5;
      out[n++] = bounds5d::Add(
          bounds5d::Scale(2.0, ViewDisplacement(pool, triple, d, mid, ball_multiplier)),
          bounds5d::Scale(-0.5, bounds5d::Add(out[i], out[j])));
    }
  }
  return out;
}

// Center screening of all triples: (score, triple index), best first for
// the top `keep`.
std::vector<std::pair<double, int>> ScreenTriples(const ContactPool &pool,
                                                  const geom5d::TriangleD &tri,
                                                  const geom5d::BoxD &box, int chart,
                                                  const std::vector<int> &inner_of, int keep) {
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
  keep = std::min<int>(keep, screened.size());
  std::partial_sort(screened.begin(), screened.begin() + keep, screened.end(),
                    [](const auto &a, const auto &b) { return a.first > b.first; });
  screened.resize(keep);
  return screened;
}

std::array<int, 3> InnerOf(const std::vector<int> &inner_of, const Triple &tr) {
  return {inner_of[tr.c[0]], inner_of[tr.c[1]], inner_of[tr.c[2]]};
}
}  // namespace

double DisplacementLower(const ContactPool &pool, const Triple &triple,
                         const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
                         const geom5d::BoxD &box, int chart, double ball_multiplier) {
  double lower = 1e300;
  for (const Quad &q : ViewControls(pool, triple, inner, tri, chart, ball_multiplier)) {
    lower = std::min(lower, bounds5d::BernsteinLower(q, box));
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
  for (const auto &[score, t] : ScreenTriples(pool, tri, box, chart, inner_of, max_full)) {
    const Triple &tr = pool.triples[t];
    const std::array<int, 3> inner = InnerOf(inner_of, tr);
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

std::vector<double> MixtureColumn(const ContactPool &pool, const Triple &triple,
                                  const std::array<int, 3> &inner, const geom5d::TriangleD &tri,
                                  const geom5d::BoxD &box, int chart) {
  const double charge = bounds5d::DBound(box) * triple.weighted_defect_upper;
  std::vector<double> col;
  col.reserve(6 * 27);
  for (const Quad &q : ViewControls(pool, triple, inner, tri, chart, 0.0)) {
    for (double c : bounds5d::BernsteinCoefficients(q, box)) col.push_back(c - charge);
  }
  return col;
}

Mixture BestMixture(const ContactPool &pool, const geom5d::TriangleD &tri,
                    const geom5d::BoxD &box, int chart, int max_components, int candidates) {
  Mixture best;
  if (pool.triples.empty()) return best;
  const std::vector<int> inner_of = BestInner(pool, tri, box, chart);
  const auto screened = ScreenTriples(pool, tri, box, chart, inner_of, candidates);
  std::vector<std::vector<double>> cols;
  for (const auto &[score, t] : screened) {
    cols.push_back(MixtureColumn(pool, pool.triples[t], InnerOf(inner_of, pool.triples[t]), tri, box, chart));
  }
  const double err = bounds5d::DisplacementError(box);
  // Start from the best single column.
  std::vector<int> chosen;
  {
    int bi = 0;
    double bv = -1e300;
    for (size_t c = 0; c < cols.size(); c++) {
      const double v = *std::min_element(cols[c].begin(), cols[c].end());
      if (v > bv) {
        bv = v;
        bi = c;
      }
    }
    chosen.push_back(bi);
  }
  auto solve = [&](const std::vector<int> &set) {
    std::vector<std::vector<double>> a;
    for (int c : set) a.push_back(cols[c]);
    return lp5d::SolveMaxMin(a);
  };
  lp5d::MaxMin mm = solve(chosen);
  while ((int)chosen.size() < max_components) {
    // The bottleneck coefficient of the current mixture.
    int bottleneck = 0;
    double low = 1e300;
    for (size_t r = 0; r < cols[0].size(); r++) {
      double v = 0.0;
      for (size_t k = 0; k < chosen.size(); k++) v += mm.w[k] * cols[chosen[k]][r];
      if (v < low) {
        low = v;
        bottleneck = r;
      }
    }
    int add = -1;
    double add_v = low;
    for (size_t c = 0; c < cols.size(); c++) {
      if (std::find(chosen.begin(), chosen.end(), (int)c) != chosen.end()) continue;
      if (cols[c][bottleneck] > add_v) {
        add_v = cols[c][bottleneck];
        add = c;
      }
    }
    if (add < 0) break;
    std::vector<int> trial = chosen;
    trial.push_back(add);
    const lp5d::MaxMin tmm = solve(trial);
    if (!(tmm.value > mm.value)) break;
    chosen = trial;
    mm = tmm;
  }
  for (size_t k = 0; k < chosen.size(); k++) {
    const int t = screened[chosen[k]].second;
    best.triples.push_back(t);
    best.inner.push_back(InnerOf(inner_of, pool.triples[t]));
    best.w.push_back(mm.w[k]);
  }
  best.margin = mm.value - err;
  return best;
}

std::vector<BigRat> RationalWeights(const std::vector<double> &w) {
  CHECK(!w.empty());
  constexpr int64_t kScale = int64_t{1} << 40;
  double total = 0.0;
  for (double x : w) total += std::max(0.0, x);
  CHECK(total > 0.0);
  // Integer numerators over 2^40: the first K-1 rounded down after
  // normalizing (the LP's weights can sum to 1 + 1e-12), the last taking the
  // remainder, which is kept nonnegative.
  std::vector<int64_t> num(w.size(), 0);
  int64_t sum = 0;
  for (size_t k = 0; k + 1 < w.size(); k++) {
    num[k] = (int64_t)std::floor(std::max(0.0, w[k]) / total * (double)kScale);
    sum += num[k];
  }
  while (sum > kScale) {
    const size_t big = std::max_element(num.begin(), num.end() - 1) - num.begin();
    const int64_t cut = std::min(num[big], sum - kScale);
    num[big] -= cut;
    sum -= cut;
  }
  num.back() = kScale - sum;
  std::vector<BigRat> out;
  for (int64_t n : num) out.push_back(BigRat(n, kScale));
  return out;
}

exact5d::MixedBox ExactMixedBox(const ContactPool &pool, const std::vector<int> &triples,
                                const std::vector<std::array<int, 3>> &inner,
                                const std::vector<BigRat> &weights,
                                const exact5d::TriangleQ &tri, const geom5d::BoxQ &box,
                                int chart) {
  CHECK(!triples.empty() && triples.size() <= 4 && triples.size() == weights.size());
  exact5d::MixedBox m;
  m.interval = geom5d::ToInterval(box);
  m.triangle = tri;
  m.chart = chart;
  for (int k = 0; k < 4; k++) {
    const int src = k < (int)triples.size() ? k : 0;
    m.component[k].certificate = contacts5d::ToAxisCertificate(pool, pool.triples[triples[src]], tri);
    m.component[k].inner_index = inner[src];
    m.component[k].ball_multiplier = exact5d::Q(0);
    m.weight[k] = k < (int)triples.size() ? weights[k] : BigRat(0);
  }
  return m;
}

}  // namespace cert5d
