// First-order rigidity margin of the identity pose of a polyhedron, and a
// search for near-identity Rupert passages at a view. See rigidity-margin.h.

#include "rigidity-margin.h"

#include <algorithm>
#include <atomic>
#include <tuple>
#include <array>
#include <cmath>
#include <limits>
#include <numbers>
#include <optional>
#include <vector>

#include "base/logging.h"
#include "geom/hull-2d.h"
#include "yocto-math.h"

namespace rigidity {

constexpr double kMergeAngle = 1e-7;
// Projected hull edges shorter than this (for circumradius ~1) are collapsed.
constexpr double kMinEdge = 1e-9;


double Cross2(const vec2 &a, const vec2 &b) { return a.x * b.y - a.y * b.x; }

// Dense simplex for: maximize c.x subject to A x <= b, x >= 0, where
// b >= 0 (so x = 0 is feasible). Bland's rule, so it cannot cycle.
// Returns nullopt if unbounded (or if the iteration cap is hit).
struct LPResult {
  double value = 0.0;
  std::vector<double> x;
};
static std::optional<LPResult> SimplexMax(const std::vector<std::vector<double>> &A,
                                          const std::vector<double> &b,
                                          const std::vector<double> &c) {
  constexpr double kEps = 1e-12;
  // Pivot elements below this are not used: pivoting on a tiny element in
  // this unscaled tableau gave wrong optima (coefficients here are O(1)).
  constexpr double kPivotEps = 1e-9;
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

  for (int iter = 0; iter < 10000; iter++) {
    int enter = -1;
    for (int j = 0; j < n + m; j++) {
      if (At(m, j) < -kEps) { enter = j; break; }
    }
    if (enter < 0) {
      LPResult res;
      res.value = At(m, cols - 1);
      res.x.assign(n, 0.0);
      for (int i = 0; i < m; i++)
        if (basis[i] < n) res.x[basis[i]] = At(i, cols - 1);
      return res;
    }
    int leave = -1;
    double best = 0.0;
    for (int i = 0; i < m; i++) {
      if (At(i, enter) > kPivotEps) {
        const double ratio = At(i, cols - 1) / At(i, enter);
        if (leave < 0 || ratio < best - kEps ||
            (ratio <= best + kEps && basis[i] < basis[leave])) {
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


// Big constant used to make the LPs start feasible at x = 0.
static double BigM(const std::vector<Constraint> &cons) {
  double mx = 0.0;
  for (const Constraint &k : cons)
    mx = std::max(mx, std::abs(k.a.x) + std::abs(k.a.y) + std::abs(k.a.z));
  return 1.0 + 2.0 * mx;
}

// f(w) = min_t max_j (a_j . w + n_j . t) for a fixed w.
double EvalF(const std::vector<Constraint> &cons, const vec3 &w) {
  // Variables tpx, tmx, tpy, tmy, s'' with s = M - s''.
  const double M = BigM(cons) * std::max(1.0, yocto::length(w));
  std::vector<std::vector<double>> A;
  std::vector<double> b;
  for (const Constraint &k : cons) {
    A.push_back({k.n.x, -k.n.x, k.n.y, -k.n.y, 1.0});
    b.push_back(M - yocto::dot(k.a, w));
  }
  auto r = SimplexMax(A, b, {0, 0, 0, 0, 1.0});
  if (!r.has_value()) {
    fprintf(stderr, "EvalF: LP failed (%zu constraints)\n", cons.size());
    return std::numeric_limits<double>::quiet_NaN();
  }
  return M - r->value;
}

// min over the cube face {w : w_c = sign, other coords in [-1, 1]} of f.
std::pair<double, vec3> MinOnCubeFace(const std::vector<Constraint> &cons,
                                             int c, double sign) {
  const int i1 = (c + 1) % 3, i2 = (c + 2) % 3;
  const double M = BigM(cons);
  // Variables: w1, w2 in [0, 2] (w_i = w - 1), tpx, tmx, tpy, tmy, s''.
  std::vector<std::vector<double>> A;
  std::vector<double> b;
  for (const Constraint &k : cons) {
    A.push_back({k.a[i1], k.a[i2], k.n.x, -k.n.x, k.n.y, -k.n.y, 1.0});
    b.push_back(M - sign * k.a[c] + k.a[i1] + k.a[i2]);
  }
  A.push_back({1, 0, 0, 0, 0, 0, 0}); b.push_back(2.0);
  A.push_back({0, 1, 0, 0, 0, 0, 0}); b.push_back(2.0);
  auto r = SimplexMax(A, b, {0, 0, 0, 0, 0, 0, 1.0});
  if (!r.has_value()) {
    // Unbounded: the constraint normals do not surround the origin (a
    // degenerate silhouette). Reported as -infinity so callers see the view.
    vec3 w{0, 0, 0};
    w[c] = sign;
    return {-std::numeric_limits<double>::infinity(), w};
  }
  vec3 w;
  w[c] = sign;
  w[i1] = r->x[0] - 1.0;
  w[i2] = r->x[1] - 1.0;
  return {M - r->value, w};
}

// Silhouette constraints at view u (empty if degenerate).
std::vector<Constraint> SilhouetteConstraints(const std::vector<vec3> &verts, vec3 u,
                                              bool robust) {
  u = yocto::normalize(u);
  vec3 axis = std::abs(u.x) < std::abs(u.y)
      ? (std::abs(u.x) < std::abs(u.z) ? vec3{1, 0, 0} : vec3{0, 0, 1})
      : (std::abs(u.y) < std::abs(u.z) ? vec3{0, 1, 0} : vec3{0, 0, 1});
  const vec3 f = yocto::normalize(yocto::cross(u, axis));
  const vec3 g = yocto::cross(u, f);
  const int nv = verts.size();
  std::vector<vec2> p(nv);
  for (int k = 0; k < nv; k++) p[k] = vec2{yocto::dot(verts[k], f), yocto::dot(verts[k], g)};

  std::vector<int> hull = Hull2D::QuickHull(p);
  if (hull.size() < 3) return {};
  // Make counterclockwise.
  double area = 0;
  for (size_t i = 0; i < hull.size(); i++)
    area += Cross2(p[hull[i]], p[hull[(i + 1) % hull.size()]]);
  if (area < 0) std::reverse(hull.begin(), hull.end());

  // Collapse hull vertices closer than kMinEdge to the previous one into a
  // single corner: the normal of such a tiny edge is numerically
  // meaningless (at views where two vertices nearly coincide in projection
  // it flipped the margin's sign), and first-order analysis only applies to
  // rotations much smaller than the edge anyway. A collapsed vertex is
  // constrained by both edges at its corner.
  std::vector<std::vector<int>> attached(nv);
  for (bool again = true; again && hull.size() > 3;) {
    again = false;
    for (size_t i = 0; i < hull.size(); i++) {
      const size_t j = (i + 1) % hull.size();
      if (yocto::length(p[hull[j]] - p[hull[i]]) < kMinEdge) {
        attached[hull[i]].push_back(hull[j]);
        for (int k : attached[hull[j]]) attached[hull[i]].push_back(k);
        hull.erase(hull.begin() + j);
        again = true;
        break;
      }
    }
  }

  // Merge hull vertices whose exterior angle is below kMergeAngle into
  // the straight edge through their neighbors. (Nearly parallel edge
  // normals make the LP ill-conditioned, and within ~1e-7 the distinction
  // does not matter for margins we care about.) Merged vertices, and any
  // other vertex lying on an edge, are constrained by that edge's normal
  // in true mode and ignored in robust mode.
  bool changed = true;
  while (changed && hull.size() > 3) {
    changed = false;
    for (size_t i = 0; i < hull.size(); i++) {
      const vec2 &pa = p[hull[(i + hull.size() - 1) % hull.size()]];
      const vec2 &pb = p[hull[i]];
      const vec2 &pc = p[hull[(i + 1) % hull.size()]];
      const vec2 d1 = yocto::normalize(pb - pa), d2 = yocto::normalize(pc - pb);
      const double ext = std::atan2(Cross2(d1, d2), yocto::dot(d1, d2));
      if (ext < kMergeAngle) {
        hull.erase(hull.begin() + i);
        changed = true;
        break;
      }
    }
  }

  std::vector<Constraint> cons;
  const int H = hull.size();
  for (int i = 0; i < H; i++) {
    const int ia = hull[i], ib = hull[(i + 1) % H];
    const vec2 d = p[ib] - p[ia];
    const double len = yocto::length(d);
    if (len < 1e-12) continue;
    const vec2 n = vec2{d.y / len, -d.x / len};  // outward for CCW
    const vec3 N = f * n.x + g * n.y;
    cons.push_back({n, yocto::cross(verts[ia], N)});
    cons.push_back({n, yocto::cross(verts[ib], N)});
    for (int c : {ia, ib}) {
      for (int k : attached[c]) cons.push_back({n, yocto::cross(verts[k], N)});
    }
    if (!robust) {
      for (int k = 0; k < nv; k++) {
        if (k == ia || k == ib) continue;
        const vec2 q = p[k] - p[ia];
        const double along = yocto::dot(q, d) / (len * len);
        if (along > 0 && along < 1 && std::abs(yocto::dot(q, n)) < kMergeAngle * len)
          cons.push_back({n, yocto::cross(verts[k], N)});
      }
    }
  }
  return cons;
}

std::atomic<int64_t> lp_fallbacks{0};

// min of f over the cube face w[c] = sign without the face LP: a grid, then
// pattern search (f is convex there), using only EvalF.
static std::pair<double, vec3> MinOnCubeFaceSearch(const std::vector<Constraint> &cons, int c,
                                                   double sign) {
  const int i1 = (c + 1) % 3, i2 = (c + 2) % 3;
  auto at = [&](double x, double y) {
    vec3 w{0, 0, 0};
    w[c] = sign;
    w[i1] = std::clamp(x, -1.0, 1.0);
    w[i2] = std::clamp(y, -1.0, 1.0);
    return w;
  };
  constexpr int kGrid = 40;
  double best = std::numeric_limits<double>::infinity(), bx = 0, by = 0;
  for (int i = 0; i <= kGrid; i++) {
    for (int j = 0; j <= kGrid; j++) {
      const double x = -1 + 2.0 * i / kGrid, y = -1 + 2.0 * j / kGrid;
      const double f = EvalF(cons, at(x, y));
      if (f < best) { best = f; bx = x; by = y; }
    }
  }
  for (double step = 2.0 / kGrid; step > 1e-12; step *= 0.5) {
    for (bool improved = true; improved;) {
      improved = false;
      for (int k = 0; k < 8; k++) {
        const double x = bx + step * std::cos(k * std::numbers::pi / 4);
        const double y = by + step * std::sin(k * std::numbers::pi / 4);
        const vec3 w = at(x, y);
        const double f = EvalF(cons, w);
        if (f < best) { best = f; bx = w[i1]; by = w[i2]; improved = true; }
      }
    }
  }
  return {best, at(bx, by)};
}

Margin FirstOrderMargin(const std::vector<vec3> &verts, vec3 u, bool robust) {
  const std::vector<Constraint> cons = SilhouetteConstraints(verts, u, robust);
  if (cons.size() < 3) return Margin{};
  Margin best;
  best.m = std::numeric_limits<double>::infinity();
  for (int c = 0; c < 3; c++) {
    for (double sign : {1.0, -1.0}) {
      auto [val, w] = MinOnCubeFace(cons, c, sign);
      // The face LP occasionally returns a value that f does not attain at
      // its own minimizer (degenerate instances). Check it with a direct
      // evaluation, and on disagreement fall back to a search.
      const double check = EvalF(cons, w);
      if (!(std::abs(check - val) <= 1e-9 * (1 + std::abs(val)))) {
        lp_fallbacks++;
        std::tie(val, w) = MinOnCubeFaceSearch(cons, c, sign);
      }
      if (val < best.m) { best.m = val; best.axis = w; }
    }
  }
  best.m_euclid_upper = EvalF(cons, best.axis / yocto::length(best.axis));
  best.axis = yocto::normalize(best.axis);
  return best;
}

// Local minimization of the (true) margin over views near u0.
std::pair<double, vec3> RefineView(const std::vector<vec3> &verts, vec3 u0) {
  u0 = yocto::normalize(u0);
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0}));
  vec3 e2 = yocto::cross(u0, e1);
  vec3 best_u = u0;
  double best = FirstOrderMargin(verts, u0, false).m;
  for (double step = 1e-3; step > 1e-11; step *= 0.5) {
    for (bool improved = true; improved;) {
      improved = false;
      for (int k = 0; k < 8; k++) {
        const double a = std::cos(k * std::numbers::pi / 4), b = std::sin(k * std::numbers::pi / 4);
        const vec3 u = yocto::normalize(best_u + (e1 * a + e2 * b) * step);
        const double m = FirstOrderMargin(verts, u, false).m;
        if (m < best) { best = m; best_u = u; improved = true; }
      }
    }
  }
  return {best, best_u};
}

// Best clearance (max over translations, by an exact LP over outer hull
// edges) of the inner copy rotated by theta about axis, at outer view u.
// Positive means a Rupert passage. Computed in difference form (inner =
// outer + delta, with delta computed accurately), so that its absolute
// error scales with theta rather than with the polyhedron: near the
// identity, clearances of 1e-12 are meaningful.
double PassageClearance(const std::vector<vec3> &verts, vec3 u, vec3 axis, double theta) {
  u = yocto::normalize(u);
  axis = yocto::normalize(axis);
  vec3 ax = std::abs(u.x) < std::abs(u.y)
      ? (std::abs(u.x) < std::abs(u.z) ? vec3{1, 0, 0} : vec3{0, 0, 1})
      : (std::abs(u.y) < std::abs(u.z) ? vec3{0, 1, 0} : vec3{0, 0, 1});
  const vec3 f = yocto::normalize(yocto::cross(u, ax)), g = yocto::cross(u, f);
  const int nv = verts.size();
  std::vector<vec2> outer(nv), delta(nv);
  const double sn = std::sin(theta);
  const double omc = 2.0 * std::sin(0.5 * theta) * std::sin(0.5 * theta);  // 1 - cos
  for (int k = 0; k < nv; k++) {
    const vec3 &v = verts[k];
    outer[k] = vec2{yocto::dot(v, f), yocto::dot(v, g)};
    // R v - v = sin(theta) (a x v) + (1 - cos(theta)) (a x (a x v)).
    const vec3 axv = yocto::cross(axis, v);
    const vec3 d = axv * sn + yocto::cross(axis, axv) * omc;
    delta[k] = vec2{yocto::dot(d, f), yocto::dot(d, g)};
  }
  std::vector<int> hull = Hull2D::QuickHull(outer);
  const int H = hull.size();
  if (H < 3) return -1.0;
  double area = 0;
  for (int i = 0; i < H; i++) area += Cross2(outer[hull[i]], outer[hull[(i + 1) % H]]);
  if (area < 0) std::reverse(hull.begin(), hull.end());
  // Maximize s subject to n_i . t + s <= g_i, where
  //   g_i = min_k [ n_i . (o_a - o_k) - n_i . delta_k ]
  // (o_a an endpoint of edge i; the endpoints themselves contribute exactly
  // -n_i . delta). With s = s1 - M (s1 >= 0) and t = tp - tm, each RHS
  // g_i + M is >= 0.
  std::vector<vec2> ns;
  std::vector<double> gs;
  double big = 0;
  for (int i = 0; i < H; i++) {
    const int ia = hull[i], ib = hull[(i + 1) % H];
    const vec2 d = outer[ib] - outer[ia];
    const double len = yocto::length(d);
    if (len < 1e-14) continue;
    const vec2 n{d.y / len, -d.x / len};
    double gi = std::numeric_limits<double>::infinity();
    for (int k = 0; k < nv; k++) {
      const double base = (k == ia || k == ib) ? 0.0 : yocto::dot(n, outer[ia] - outer[k]);
      gi = std::min(gi, base - yocto::dot(n, delta[k]));
    }
    ns.push_back(n);
    gs.push_back(gi);
    big = std::max(big, std::abs(gi));
  }
  // SimplexMax uses absolute tolerances, so normalize the right-hand
  // sides to O(1) (they can be ~1e-12 near the identity) and scale back.
  const double scale = big > 0 ? big : 1.0;
  const double M = 2.0;
  std::vector<std::vector<double>> A;
  std::vector<double> b;
  for (size_t i = 0; i < ns.size(); i++) {
    A.push_back({ns[i].x, -ns[i].x, ns[i].y, -ns[i].y, 1.0});
    b.push_back(gs[i] / scale + M);
  }
  auto r = SimplexMax(A, b, {0, 0, 0, 0, 1.0});
  if (!r.has_value()) return -1.0;
  return (r->value - M) * scale;
}

// Local search for a passage near view u0: maximize the clearance over
// log(theta), the rotation axis, and the outer view. Returns the best
// clearance found (positive = Rupert passage) and its parameters.
PassageResult SearchPassage(const std::vector<vec3> &verts, vec3 u0, vec3 axis0) {
  PassageResult best{-1e300, u0, axis0, 0};
  auto Perp = [](const vec3 &v) {
    vec3 e1 = yocto::normalize(yocto::cross(v, std::abs(v.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0}));
    return std::make_pair(e1, yocto::cross(v, e1));
  };
  for (double theta0 : {1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3}) {
    for (double sign : {1.0, -1.0}) {
      vec3 u = yocto::normalize(u0), ax = yocto::normalize(axis0 * sign);
      double lt = std::log(theta0);
      double cur = PassageClearance(verts, u, ax, theta0);
      // Pattern search in 5 dims: 2 for u, 2 for the axis, 1 for log(theta).
      for (double step = 1e-2; step > 1e-10; step *= 0.5) {
        for (bool improved = true; improved;) {
          improved = false;
          for (int dim = 0; dim < 5; dim++) {
            for (double sg : {1.0, -1.0}) {
              vec3 u2 = u, a2 = ax;
              double lt2 = lt;
              if (dim < 2) {
                auto [e1, e2] = Perp(u);
                u2 = yocto::normalize(u + (dim == 0 ? e1 : e2) * (sg * step * 0.1));
              } else if (dim < 4) {
                auto [e1, e2] = Perp(ax);
                a2 = yocto::normalize(ax + (dim == 2 ? e1 : e2) * (sg * step));
              } else {
                // Keep theta >= 1e-12: at theta -> 0 the clearance tends to
                // exactly 0 (the identity), which is not a passage.
                lt2 = std::max(std::log(1e-12), lt + sg * step * 50);
              }
              const double v = PassageClearance(verts, u2, a2, std::exp(lt2));
              if (v > cur) { cur = v; u = u2; ax = a2; lt = lt2; improved = true; }
            }
          }
        }
      }
      if (cur > best.clearance) best = {cur, u, ax, std::exp(lt)};
    }
  }
  return best;
}

PassageResult SearchPassageAt(const std::vector<vec3> &verts, vec3 u0, vec3 axis0, double theta) {
  auto Perp = [](const vec3 &v) {
    vec3 e1 = yocto::normalize(yocto::cross(v, std::abs(v.z) < 0.9 ? vec3{0, 0, 1} : vec3{1, 0, 0}));
    return std::make_pair(e1, yocto::cross(v, e1));
  };
  vec3 u = yocto::normalize(u0), ax = yocto::normalize(axis0);
  double cur = PassageClearance(verts, u, ax, theta);
  // Pattern search in 4 dims: 2 for the view, 2 for the axis.
  for (double step = 1e-1; step > 1e-10; step *= 0.5) {
    for (bool improved = true; improved;) {
      improved = false;
      for (int dim = 0; dim < 4; dim++) {
        for (double sg : {1.0, -1.0}) {
          vec3 u2 = u, a2 = ax;
          if (dim < 2) {
            auto [e1, e2] = Perp(u);
            u2 = yocto::normalize(u + (dim == 0 ? e1 : e2) * (sg * step * 0.1));
          } else {
            auto [e1, e2] = Perp(ax);
            a2 = yocto::normalize(ax + (dim == 2 ? e1 : e2) * (sg * step));
          }
          const double v = PassageClearance(verts, u2, a2, theta);
          if (v > cur) { cur = v; u = u2; ax = a2; improved = true; }
        }
      }
    }
  }
  return {cur, u, ax, theta};
}

}  // namespace rigidity
