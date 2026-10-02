#include "cert5d.h"

#include <cmath>
#include <cstdio>
#include <random>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "contacts5d.h"
#include "exact5d.h"
#include "geom5d.h"
#include "rapidjson/document.h"
#include "util.h"

using exact5d::Q;

static std::vector<exact5d::TriangleQ> CodeTriangles() {
  rapidjson::Document doc;
  doc.Parse(Util::ReadFile("codebdd231.json").c_str());
  CHECK(!doc.HasParseError());
  std::vector<exact5d::TriangleQ> out;
  for (const auto &code : doc["codes"].GetArray()) {
    for (const auto &t : code["triangles"].GetArray()) {
      exact5d::TriangleQ tri;
      for (int i = 0; i < 3; i++) {
        tri[i] = {Q(std::string_view(t[i]["x"].GetString())), Q(std::string_view(t[i]["y"].GetString())),
                  Q(std::string_view(t[i]["z"].GetString()))};
      }
      out.push_back(tri);
    }
  }
  return out;
}

// A box of half-width 2^-k around a dyadic point, inside the chart's root.
static geom5d::BoxQ SmallBox(std::mt19937_64 &rng, int chart, int k) {
  geom5d::BoxQ b = geom5d::RootBox(chart);
  for (int step = 0; step < 3 * k; step++) {
    const int axis = geom5d::WidestAxis(geom5d::ToDouble(b));
    b = (rng() % 2) ? geom5d::LowerHalf(b, axis) : geom5d::UpperHalf(b, axis);
  }
  return b;
}

int main() {
  const auto tris = CodeTriangles();
  std::mt19937_64 rng(11);
  int evaluated = 0, positive = 0, valid = 0;
  for (int n = 0; n < 40; n++) {
    const int chart = rng() % 3;
    exact5d::TriangleQ tq = tris[rng() % tris.size()];
    std::string path;
    for (int d = 0; d < 6; d++) path += (char)('0' + rng() % 4);
    tq = geom5d::SplitTrianglePath(tq, path);
    const geom5d::TriangleD td = geom5d::ToDouble(tq);
    const geom5d::BoxQ bq = SmallBox(rng, chart, 6);
    const geom5d::BoxD bd = geom5d::ToDouble(bq);
    contacts5d::PoolParams params;
    const auto pool = contacts5d::BuildContactPool(td, params);
    if (pool.triples.empty()) continue;
    const cert5d::Single s = cert5d::BestSingle(pool, td, bd, chart);
    if (s.triple < 0) continue;
    evaluated++;

    const exact5d::GlobalBox g = cert5d::ExactGlobalBox(pool, s, tq, bq, chart);
    CHECK(exact5d::Admissible(g));
    // The double Bernstein bound mirrors the exact one.
    const double lower_d =
        cert5d::DisplacementLower(pool, pool.triples[s.triple], s.inner, td, bd, chart);
    const double lower_q = exact5d::BernsteinDisplacementLower(g).ToDouble();
    CHECK(std::abs(lower_d - lower_q) <= 1e-12 * (1.0 + std::abs(lower_q)))
        << lower_d << " vs " << lower_q;
    // The double margin is conservative (Bernstein only, larger defect).
    const double slack = exact5d::DisplacementSlack(g).ToDouble();
    CHECK(s.margin <= slack + 1e-12 * (1.0 + std::abs(slack))) << s.margin << " vs " << slack;
    const bool v = exact5d::Valid(g);
    if (s.margin > 1e-9) {
      positive++;
      CHECK(v) << "double margin " << s.margin << " but exact invalid (slack " << slack << ")";
    }
    valid += v;
  }
  printf("%d boxes evaluated: %d with positive double margin, %d exactly Valid\n", evaluated,
         positive, valid);
  CHECK(valid > 0) << "expected some certified boxes";

  // Rational weights are nonnegative and sum to exactly 1, even when the LP's
  // weights overshoot 1 slightly.
  for (const std::vector<double> &w : std::vector<std::vector<double>>{
           {0.5, 0.5 + 1e-12}, {0.3, 0.7 + 1e-12, 1e-13}, {1.0}, {0.25, 0.25, 0.25, 0.25 + 3e-12}}) {
    const auto q = cert5d::RationalWeights(w);
    BigRat sum(0);
    for (const auto &x : q) {
      CHECK(!(x < BigRat(0)));
      sum = sum + x;
    }
    CHECK(sum == BigRat(1));
  }

  // Mixtures, on larger boxes (where single triples often fail).
  int mixed_tried = 0, single_ok = 0, mixed_ok = 0, mixed_valid = 0;
  for (int n = 0; n < 40; n++) {
    const int chart = rng() % 3;
    exact5d::TriangleQ tq = tris[rng() % tris.size()];
    std::string path;
    for (int d = 0; d < 4; d++) path += (char)('0' + rng() % 4);
    tq = geom5d::SplitTrianglePath(tq, path);
    const geom5d::TriangleD td = geom5d::ToDouble(tq);
    const geom5d::BoxQ bq = SmallBox(rng, chart, 3);
    const geom5d::BoxD bd = geom5d::ToDouble(bq);
    const auto pool = contacts5d::BuildContactPool(td, contacts5d::PoolParams{});
    if (pool.triples.empty()) continue;
    const cert5d::Single s = cert5d::BestSingle(pool, td, bd, chart);
    const cert5d::Mixture m = cert5d::BestMixture(pool, td, bd, chart);
    mixed_tried++;
    single_ok += s.margin > 0;
    CHECK(m.margin >= s.margin - 1e-12 * (1 + std::abs(s.margin))) << m.margin << " < " << s.margin;
    if (m.margin > 1e-9) {
      mixed_ok++;
      const auto weights = cert5d::RationalWeights(m.w);
      BigRat sum(0);
      for (const auto &w : weights) {
        CHECK(!(w < BigRat(0)));
        sum = sum + w;
      }
      CHECK(sum == BigRat(1));
      const exact5d::MixedBox mb = cert5d::ExactMixedBox(pool, m.triples, m.inner, weights, tq, bq, chart);
      const bool v = exact5d::Valid(mb);
      CHECK(v) << "mixture margin " << m.margin << " but exact invalid (slack "
               << exact5d::DisplacementSlack(mb).ToDouble() << ")";
      mixed_valid += v;
    }
  }
  printf("%d larger boxes: single certifies %d, mixture %d (%d exactly Valid)\n", mixed_tried,
         single_ok, mixed_ok, mixed_valid);
  printf("cert5d tests PASSED\n");
  return 0;
}
