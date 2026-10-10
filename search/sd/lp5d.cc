#include "lp5d.h"

#include <algorithm>
#include <cmath>
#include <limits>

#include "base/logging.h"

namespace lp5d {

std::optional<LPResult> SimplexMax(const std::vector<std::vector<double>> &A,
                                   const std::vector<double> &b,
                                   const std::vector<double> &c) {
  constexpr double kEps = 1e-12;
  const int m = A.size(), n = c.size();
  const int cols = n + m + 1;
  std::vector<double> T((m + 1) * cols, 0.0);
  auto At = [&](int r, int k) -> double & { return T[r * cols + k]; };
  std::vector<int> basis(m);
  for (int i = 0; i < m; i++) {
    CHECK(b[i] >= 0.0);
    for (int j = 0; j < n; j++) At(i, j) = A[i][j];
    At(i, n + i) = 1.0;
    At(i, cols - 1) = b[i];
    basis[i] = n + i;
  }
  for (int j = 0; j < n; j++) At(m, j) = -c[j];

  for (int iter = 0; iter < 100000; iter++) {
    int enter = -1;
    for (int j = 0; j < n + m; j++) {
      if (At(m, j) < -kEps) {
        enter = j;
        break;
      }
    }
    if (enter < 0) {
      LPResult res;
      res.value = At(m, cols - 1);
      res.x.assign(n, 0.0);
      for (int i = 0; i < m; i++) {
        if (basis[i] < n) res.x[basis[i]] = At(i, cols - 1);
      }
      return res;
    }
    int leave = -1;
    double best = 0.0;
    for (int i = 0; i < m; i++) {
      if (At(i, enter) > kEps) {
        const double ratio = At(i, cols - 1) / At(i, enter);
        if (leave < 0 || ratio < best - kEps || (ratio <= best + kEps && basis[i] < basis[leave])) {
          leave = i;
          best = ratio;
        }
      }
    }
    if (leave < 0) return std::nullopt;  // unbounded
    const double piv = At(leave, enter);
    for (int k = 0; k < cols; k++) At(leave, k) /= piv;
    for (int r = 0; r <= m; r++) {
      if (r == leave) continue;
      const double f = At(r, enter);
      if (f == 0.0) continue;
      for (int k = 0; k < cols; k++) At(r, k) -= f * At(leave, k);
    }
    basis[leave] = enter;
  }
  return std::nullopt;
}

MaxMin SolveMaxMin(const std::vector<std::vector<double>> &a) {
  const int K = a.size();
  CHECK(K >= 1);
  const int R = a[0].size();
  auto value_of = [&](const std::vector<double> &w) {
    double v = std::numeric_limits<double>::infinity();
    for (int r = 0; r < R; r++) {
      double s = 0.0;
      for (int k = 0; k < K; k++) s += w[k] * a[k][r];
      v = std::min(v, s);
    }
    return v;
  };
  if (K == 1) return MaxMin{.w = {1.0}, .value = value_of({1.0})};
  // The optimal weights do not change when every column is scaled by the
  // same positive factor, so solve with the entries normalized to at most 1
  // in magnitude: the simplex tolerances are absolute, and near the identity
  // the entries are around 1e-13.
  double scale = 0.0;
  for (const auto &col : a) for (double v : col) scale = std::max(scale, std::abs(v));
  if (!(scale > 0.0) || !std::isfinite(scale)) scale = 1.0;
  // Eliminate w_K = 1 - sum_{k<K} w_k and shift t = s - M so that the
  // constraints  s - sum_{k<K} w_k (a_k,r - a_K,r) <= M + a_K,r  have a
  // nonnegative right side; also sum_{k<K} w_k <= 1.
  const double M = 2.0;
  const int n = K;  // w_1..w_{K-1}, s
  std::vector<std::vector<double>> A;
  std::vector<double> b;
  for (int r = 0; r < R; r++) {
    std::vector<double> row(n, 0.0);
    for (int k = 0; k < K - 1; k++) row[k] = -(a[k][r] - a[K - 1][r]) / scale;
    row[K - 1] = 1.0;
    A.push_back(row);
    b.push_back(M + a[K - 1][r] / scale);
  }
  std::vector<double> sum_row(n, 0.0);
  for (int k = 0; k < K - 1; k++) sum_row[k] = 1.0;
  A.push_back(sum_row);
  b.push_back(1.0);
  std::vector<double> c(n, 0.0);
  c[K - 1] = 1.0;
  const auto res = SimplexMax(A, b, c);
  std::vector<double> w(K, 0.0);
  if (!res.has_value()) {
    // Numerical trouble (should not happen after scaling): fall back to the
    // best single column, which is still a valid choice of weights.
    int best = 0;
    double best_value = -std::numeric_limits<double>::infinity();
    for (int k = 0; k < K; k++) {
      std::vector<double> e(K, 0.0);
      e[k] = 1.0;
      const double v = value_of(e);
      if (v > best_value) best = k, best_value = v;
    }
    w[best] = 1.0;
    return MaxMin{.w = w, .value = best_value};
  }
  double rest = 1.0;
  for (int k = 0; k < K - 1; k++) {
    w[k] = std::max(0.0, res->x[k]);
    rest -= w[k];
  }
  w[K - 1] = std::max(0.0, rest);
  return MaxMin{.w = w, .value = value_of(w)};
}

}  // namespace lp5d
