// Small dense linear programs for the 5D search.

#ifndef _NOPERT229_LP5D_H
#define _NOPERT229_LP5D_H

#include <optional>
#include <vector>

namespace lp5d {

struct LPResult {
  double value = 0.0;
  std::vector<double> x;
};

// Maximize c.x subject to A x <= b and x >= 0, where b >= 0 (so x = 0 is
// feasible). Dense tableau, Bland's rule (cannot cycle). nullopt if
// unbounded or the iteration cap is reached.
std::optional<LPResult> SimplexMax(const std::vector<std::vector<double>> &A,
                                   const std::vector<double> &b,
                                   const std::vector<double> &c);

// The best convex combination of rows: maximize min_r sum_k w_k a[k][r]
// over w >= 0 with sum_k w_k = 1. a[k] are the columns' values (all the
// same length). Returns the weights and the max-min value.
struct MaxMin {
  std::vector<double> w;
  double value = 0.0;
};
MaxMin SolveMaxMin(const std::vector<std::vector<double>> &a);

}  // namespace lp5d

#endif
