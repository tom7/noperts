#include "lp5d.h"

#include <cmath>
#include <cstdio>
#include <random>

#include "base/logging.h"

using namespace lp5d;

int main() {
  // max x + y s.t. x + 2y <= 4, 3x + y <= 6: optimum (8/5, 6/5), value 14/5.
  auto r = SimplexMax({{1, 2}, {3, 1}}, {4, 6}, {1, 1});
  CHECK(r.has_value());
  CHECK(std::abs(r->value - 2.8) < 1e-12);
  CHECK(std::abs(r->x[0] - 1.6) < 1e-12 && std::abs(r->x[1] - 1.2) < 1e-12);
  // Unbounded.
  CHECK(!SimplexMax({{1, -1}}, {1}, {0, 1}).has_value());

  // Max-min: two columns that complement each other.
  //   a0 = (1, -1), a1 = (-1, 1): best is w = (1/2, 1/2), value 0.
  auto mm = SolveMaxMin({{1, -1}, {-1, 1}});
  CHECK(std::abs(mm.value) < 1e-12);
  CHECK(std::abs(mm.w[0] - 0.5) < 1e-12);
  //   a0 = (3, -1), a1 = (-1, 1): w0 = 1/3, value 1/3.
  mm = SolveMaxMin({{3, -1}, {-1, 1}});
  CHECK(std::abs(mm.value - 1.0 / 3) < 1e-12) << mm.value;

  // Random problems: the LP optimum beats sampled weights, at any scale
  // (near the identity, the 5D search's columns are around 1e-13).
  std::mt19937_64 rng(3);
  std::normal_distribution<double> g;
  std::uniform_real_distribution<double> u(0, 1);
  for (int n = 0; n < 600; n++) {
    const double scale = n < 200 ? 1.0 : n < 400 ? 1e-13 : 1e8;
    const int K = 1 + rng() % 4, R = 1 + rng() % 162;
    std::vector<std::vector<double>> a(K, std::vector<double>(R));
    for (auto &col : a) for (double &v : col) v = scale * g(rng);
    const MaxMin best = SolveMaxMin(a);
    double sum = 0.0;
    for (double w : best.w) {
      CHECK(w >= 0.0);
      sum += w;
    }
    CHECK(std::abs(sum - 1.0) < 1e-12);
    for (int s = 0; s < 100; s++) {
      std::vector<double> w(K);
      double tot = 0.0;
      for (double &x : w) tot += (x = -std::log(u(rng)));
      double v = 1e300;
      for (int r = 0; r < R; r++) {
        double acc = 0.0;
        for (int k = 0; k < K; k++) acc += w[k] / tot * a[k][r];
        v = std::min(v, acc);
      }
      CHECK(v <= best.value + 1e-9 * scale) << v << " > " << best.value;
    }
  }
  printf("lp5d tests PASSED\n");
  return 0;
}
