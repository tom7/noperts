// Identity Tube Incremental BFS Search & Dual-Bound Engine for Nopert #229
// Implements canonical base-4 tree search using tubetree229 library.

#include <iomanip>
#include <iostream>
#include <memory>
#include <utility>
#include <vector>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <deque>
#include <cmath>
#include <chrono>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <atomic>
#include <cassert>
#include <filesystem>
#include <format>
#include <array>
#include <algorithm>
#include <numeric>
#include <set>
#include <random>
#include <ctime>
#include <csignal>

#include "ansi.h"
#include "base/logging.h"
#include "base/stringprintf.h"
#include "bignum/big-overloads.h"
#include "bignum/big-vec.h"
#include "bignum/big.h"
#include "geom/hull-2d.h"
#include "nopert229.h"
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;
using namespace tubetree229;

static std::atomic<bool> g_stop_requested{false};

static inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

static void SignalHandler(int sig) {
  g_stop_requested = true;
  std::cerr << "\n[SIGNAL] Stop requested (signal " << sig << "). Gracefully finishing in-flight tasks and saving tree...\n" << std::flush;
}

// ============================================================================
// EXACT POLYNOMIAL AND AUDIT ARITHMETIC
// ============================================================================

struct QPoly {
  BigRat c[10];
  QPoly() {
    for (int i = 0; i < 10; i++) c[i] = BigRat(0);
  }
  static QPoly MulLinear(const BigVecQ3 &a, const BigVecQ3 &b) {
    QPoly p;
    p.c[4] = a.x * b.x;
    p.c[5] = a.x * b.y + a.y * b.x;
    p.c[6] = a.x * b.z + a.z * b.x;
    p.c[7] = a.y * b.y;
    p.c[8] = a.y * b.z + a.z * b.y;
    p.c[9] = a.z * b.z;
    return p;
  }
  void AddScaled(const BigRat &s, const QPoly &o) {
    for (int i = 0; i < 10; i++) c[i] += s * o.c[i];
  }
  std::pair<BigRat, BigRat> EvalCentered(const BigVecQ3 &center, const BigVecQ3 &radius) const {
    BigRat val = c[0] + c[1] * center.x + c[2] * center.y + c[3] * center.z +
                 c[4] * center.x * center.x + c[5] * center.x * center.y +
                 c[6] * center.x * center.z + c[7] * center.y * center.y +
                 c[8] * center.y * center.z + c[9] * center.z * center.z;

    BigRat grad_x = c[1] + BigRat(2) * c[4] * center.x + c[5] * center.y + c[6] * center.z;
    BigRat grad_y = c[2] + c[5] * center.x + BigRat(2) * c[7] * center.y + c[8] * center.z;
    BigRat grad_z = c[3] + c[6] * center.x + c[8] * center.y + BigRat(2) * c[9] * center.z;

    auto abs_r = [](const BigRat &x) { return x < 0 ? -x : x; };

    BigRat lin_bound = abs_r(grad_x) * radius.x + abs_r(grad_y) * radius.y + abs_r(grad_z) * radius.z;
    BigRat quad_bound = abs_r(c[4]) * radius.x * radius.x + abs_r(c[5]) * radius.x * radius.y +
                        abs_r(c[6]) * radius.x * radius.z + abs_r(c[7]) * radius.y * radius.y +
                        abs_r(c[8]) * radius.y * radius.z + abs_r(c[9]) * radius.z * radius.z;
    return {val, lin_bound + quad_bound};
  }
};


static BigVecQ3 GetExactEdge(const ContactInfo &c) {
  const BigVecQ3 &v_start = VertexQ(c.edge_start);
  const BigVecQ3 &v_finish = VertexQ(c.edge_finish);
  const BigVecQ3 &v_start2 = VertexQ(c.edge_start2);
  const BigVecQ3 &v_finish2 = VertexQ(c.edge_finish2);
  BigRat mixQ(c.mix, 1000);
  return (v_start - v_finish) * mixQ + (v_start2 - v_finish2) * (BigRat(1) - mixQ);
}

static inline BigRat CeilTo(const BigRat &x, const BigInt &denom) {
  BigRat scaled = x * BigRat(denom);
  BigInt num = scaled.Numerator();
  BigInt den = scaled.Denominator();
  BigInt q;
  if (num >= BigInt(0)) {
    q = (num + den - BigInt(1)) / den;
  } else {
    q = num / den;
  }
  return BigRat(q, denom);
}

static inline BigRat CeilTo(const BigRat &x, int64_t denom) {
  return CeilTo(x, BigInt(denom));
}

static inline BigRat FloorTo(const BigRat &x, const BigInt &denom) {
  BigRat scaled = x * BigRat(denom);
  BigInt num = scaled.Numerator();
  BigInt den = scaled.Denominator();
  BigInt q;
  if (num >= BigInt(0)) {
    q = num / den;
  } else {
    q = (num - den + BigInt(1)) / den;
  }
  return BigRat(q, denom);
}

static inline BigRat FloorTo(const BigRat &x, int64_t denom) {
  return FloorTo(x, BigInt(denom));
}

// Barycentric coordinates of target inside tetrahedron (p0, p1, p2, p3)
static bool Barycentric4(const BigVecQ3 pts[4], const BigVecQ3 &target, BigRat lam[4]) {
  BigVecQ3 v0 = pts[0] - pts[3];
  BigVecQ3 v1 = pts[1] - pts[3];
  BigVecQ3 v2 = pts[2] - pts[3];
  BigVecQ3 w = target - pts[3];
  BigRat den = BigVecQ3::Det(v0, v1, v2);
  if (den == 0) return false;
  lam[0] = BigVecQ3::Det(w, v1, v2) / den;
  lam[1] = BigVecQ3::Det(v0, w, v2) / den;
  lam[2] = BigVecQ3::Det(v0, v1, w) / den;
  lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
  return true;
}

// Exact tetrahedron axis radius
static BigRat ExactTetrahedronAxisRadius(const BigVecQ3 pts[4]) {
  BigRat zero[4];
  if (!Barycentric4(pts, {BigRat(0), BigRat(0), BigRat(0)}, zero)) return BigRat(0);
  for (int i = 0; i < 4; i++) {
    if (zero[i] <= 0) return BigRat(0);
  }
  BigRat min_bound(1000000);
  for (int axis = 0; axis < 3; axis++) {
    for (int sign : {-1, 1}) {
      BigVecQ3 target(axis == 0 ? BigRat(sign) : BigRat(0),
                   axis == 1 ? BigRat(sign) : BigRat(0),
                   axis == 2 ? BigRat(sign) : BigRat(0));
      BigRat at_one[4];
      if (!Barycentric4(pts, target, at_one)) continue;
      for (int i = 0; i < 4; i++) {
        BigRat d = at_one[i] - zero[i];
        if (d < 0) {
          BigRat b = zero[i] / (-d);
          if (b < min_bound) min_bound = b;
        }
      }
    }
  }
  return min_bound;
}

// Audits a single 3-contact axis on triangle tri
static bool AuditAxis(const TriangleQ &tri, ContactInfo contacts[3], AxisCertificate *out_cert,
                      BigVecQ3 *out_center, BigRat *out_delta, std::string *fail_reason = nullptr) {
  BigVecQ3 edges[3] = {GetExactEdge(contacts[0]), GetExactEdge(contacts[1]), GetExactEdge(contacts[2])};
  BigVecQ3 coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
  BigVecQ3 coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
  BigVecQ3 coeff2 = BigVecQ3::Cross(edges[0], edges[1]);

  BigRat p0 = BigVecQ3::Dot(tri.corners[0], coeff0);
  BigRat p1 = BigVecQ3::Dot(tri.corners[0], coeff1);
  BigRat p2 = BigVecQ3::Dot(tri.corners[0], coeff2);
  if (p0 < 0 && p1 < 0 && p2 < 0) {
    std::swap(contacts[1], contacts[2]);
    std::swap(edges[1], edges[2]);
    coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
    coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
    coeff2 = BigVecQ3::Cross(edges[0], edges[1]);
  }

  BigVecQ3 w_coeffs[3] = {coeff0, coeff1, coeff2};
  BigRat support_error(6, 1000000000000000LL); // 6 / 10^15
  BigRat weight_upper[3];
  BigRat sum_weight_upper(0);

  for (int m = 0; m < 3; m++) {
    BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
    BigRat w_min = w_max;
    for (int c = 1; c < 3; c++) {
      BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
      if (val > w_max) w_max = val;
      if (val < w_min) w_min = val;
    }
    if (w_min < support_error) {
      if (fail_reason) *fail_reason = StringPrintf("w_min < support_error (m=%d, w_min=%s)", m, w_min.ToString().c_str());
      return false;
    }
    weight_upper[m] = w_max + support_error;
    sum_weight_upper = sum_weight_upper + weight_upper[m];
  }

  BigRat exact_B = sum_weight_upper * BigRat(2);
  BigRat B = CeilTo(exact_B, 1000000000LL);
  if (B <= 0) {
    if (fail_reason) *fail_reason = "B <= 0";
    return false;
  }

  out_cert->B = B;
  for (int m = 0; m < 3; m++) {
    out_cert->contacts[m] = contacts[m];
    int sel = contacts[m].vertex;
    const BigVecQ3 &v_sel = VertexQ(sel);
    BigRat best_support(1000000);
    int best_w = -1;
    for (int k = 0; k < 20; k++) {
      bool tie = (k == sel) ||
                 (contacts[m].mix == 1000 && sel == contacts[m].edge_finish && k == contacts[m].edge_start) ||
                 (contacts[m].mix == 0 && sel == contacts[m].edge_start2 && k == contacts[m].edge_finish2);
      BigRat s_upper(0);
      if (!tie) {
        const BigVecQ3 &v_k = VertexQ(k);
        BigVecQ3 delta = v_k - v_sel;
        BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta);
        BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
          if (val > max_s) max_s = val;
        }
        s_upper = max_s + support_error;
      }
      if (s_upper > 0) {
        if (fail_reason) *fail_reason = StringPrintf("s_upper > 0 (m=%d, k=%d, s=%s)", m, k, s_upper.ToString().c_str());
        return false;
      }
      if (s_upper < best_support) {
        best_support = s_upper;
        best_w = k;
      }
    }
    if (best_support >= 0) {
      if (fail_reason) *fail_reason = StringPrintf("best_support >= 0 (m=%d)", m);
      return false;
    }
    out_cert->nonzero_witness[m] = best_w;
  }

  // Bounding box over triangle
  BigVecQ3 ball_center, ball_radius;
  for (int c = 0; c < 3; c++) {
    BigRat c0 = (c == 0 ? tri.corners[0].x : c == 1 ? tri.corners[0].y : tri.corners[0].z);
    BigRat c1 = (c == 0 ? tri.corners[1].x : c == 1 ? tri.corners[1].y : tri.corners[1].z);
    BigRat c2 = (c == 0 ? tri.corners[2].x : c == 1 ? tri.corners[2].y : tri.corners[2].z);
    BigRat lo = std::min({c0, c1, c2});
    BigRat hi = std::max({c0, c1, c2});
    BigRat mid = (lo + hi) / BigRat(2);
    BigRat rad = (hi - lo) / BigRat(2);
    if (c == 0) { ball_center.x = mid; ball_radius.x = rad; }
    else if (c == 1) { ball_center.y = mid; ball_radius.y = rad; }
    else { ball_center.z = mid; ball_radius.z = rad; }
  }

  QPoly polys[3];
  for (int coord = 0; coord < 3; coord++) {
    for (int i = 0; i < 3; i++) {
      const BigVecQ3 &v_supp = VertexQ(contacts[i].vertex);
      BigVecQ3 lift_row[3] = {
        {BigRat(0), edges[i].z, -edges[i].y},
        {-edges[i].z, BigRat(0), edges[i].x},
        {edges[i].y, -edges[i].x, BigRat(0)}
      };
      BigVecQ3 cross_lift;
      if (coord == 0) {
        cross_lift = {v_supp.y * lift_row[2].x - v_supp.z * lift_row[1].x,
                      v_supp.y * lift_row[2].y - v_supp.z * lift_row[1].y,
                      v_supp.y * lift_row[2].z - v_supp.z * lift_row[1].z};
      } else if (coord == 1) {
        cross_lift = {v_supp.z * lift_row[0].x - v_supp.x * lift_row[2].x,
                      v_supp.z * lift_row[0].y - v_supp.x * lift_row[2].y,
                      v_supp.z * lift_row[0].z - v_supp.x * lift_row[2].z};
      } else {
        cross_lift = {v_supp.x * lift_row[1].x - v_supp.y * lift_row[0].x,
                      v_supp.x * lift_row[1].y - v_supp.y * lift_row[0].y,
                      v_supp.x * lift_row[1].z - v_supp.y * lift_row[0].z};
      }
      QPoly term = QPoly::MulLinear(w_coeffs[i], cross_lift);
      polys[coord].AddScaled(BigRat(1), term);
    }
  }

  std::pair<BigRat, BigRat> evals[3] = {
    polys[0].EvalCentered(ball_center, ball_radius),
    polys[1].EvalCentered(ball_center, ball_radius),
    polys[2].EvalCentered(ball_center, ball_radius)
  };

  out_center->x = evals[0].first / B;
  out_center->y = evals[1].first / B;
  out_center->z = evals[2].first / B;

  BigRat variation_error(150, 10000000000LL); // 150 * KAPPA
  BigRat exact_delta = (evals[0].second + evals[1].second + evals[2].second + BigRat(3) * variation_error) / B;
  *out_delta = CeilTo(exact_delta, 1000000000LL);
  return true;
}

static const BigRat CANDIDATE_RS[] = {
  BigRat("1/1000"), BigRat("1/2000"), BigRat("1/4000"),
  BigRat("1/5000"), BigRat("1/8000"), BigRat("1/10000"),
  BigRat("1/20000"), BigRat("1/40000"), BigRat("1/50000"),
  BigRat("1/100000"), BigRat("1/200000"), BigRat("1/250000"),
  BigRat("1/300000"), BigRat("1/400000"), BigRat("1/500000"),
  BigRat("1/1000000"), BigRat("1/2000000"), BigRat("1/3000000"),
  BigRat("1/4000000"), BigRat("1/5000000"), BigRat("1/6000000"),
  BigRat("1/8000000"), BigRat("1/10000000"), BigRat("1/20000000"),
  BigRat("1/50000000"), BigRat("1/100000000"),
  BigRat("1/200000000"), BigRat("1/500000000"),
  BigRat("1/1000000000"), BigRat("1/2000000000"),
  BigRat("1/5000000000"), BigRat("1/10000000000"),
  BigRat("1/20000000000"), BigRat("1/50000000000"),
  BigRat("1/100000000000"), BigRat("1/200000000000"), BigRat("1/500000000000"),
  BigRat("1/1000000000000"), BigRat("1/2000000000000"), BigRat("1/5000000000000"),
  BigRat("1/10000000000000"), BigRat("1/20000000000000"), BigRat("1/50000000000000"),
  BigRat("1/100000000000000"), BigRat("1/200000000000000"), BigRat("1/500000000000000"),
  BigRat("1/1000000000000000"), BigRat("1/2000000000000000"), BigRat("1/5000000000000000"),
  BigRat("1/10000000000000000"), BigRat("1/20000000000000000"), BigRat("1/50000000000000000"),
  BigRat("1/100000000000000000"), BigRat("1/200000000000000000"), BigRat("1/500000000000000000"),
  BigRat("1/1000000000000000000"), BigRat("1/2000000000000000000"), BigRat("1/5000000000000000000"),
  BigRat("1/10000000000000000000"), BigRat("1/20000000000000000000"), BigRat("1/50000000000000000000"),
  BigRat("1/100000000000000000000"), BigRat("1/200000000000000000000"), BigRat("1/500000000000000000000"),
  BigRat("1/1000000000000000000000"), BigRat("1/10000000000000000000000"),
  BigRat("1/100000000000000000000000"), BigRat("1/1000000000000000000000000"),
  BigRat("1/10000000000000000000000000") // 1e-25
};

static bool AuditCertificateAdaptive(
    const TriangleQ &tri,
    const TubeCertificate &in_cert,
    TubeCertificate *out_cert,
    std::string *fail_reason = nullptr) {

  *out_cert = in_cert;
  BigVecQ3 centers[4];
  BigRat deltas[4];
  for (int a = 0; a < 4; a++) {
    ContactInfo contacts[3] = {in_cert.axes[a].contacts[0],
                               in_cert.axes[a].contacts[1],
                               in_cert.axes[a].contacts[2]};
    std::string axis_reason;
    if (!AuditAxis(tri, contacts, &out_cert->axes[a], &centers[a], &deltas[a], &axis_reason)) {
      if (fail_reason) *fail_reason = StringPrintf("axis %d audit failed: %s", a, axis_reason.c_str());
      return false;
    }
  }

  BigRat delta = std::max({deltas[0], deltas[1], deltas[2], deltas[3]});
  BigRat axis_radius = ExactTetrahedronAxisRadius(centers);
  BigRat cover_radius = axis_radius * BigRat(19, 20) * BigRat(4, 7);
  BigRat diff = cover_radius - delta;
  if (diff <= BigRat(0)) {
    if (fail_reason) *fail_reason = StringPrintf("cover_radius - delta <= 0 (diff=%s, cover=%s, delta=%s)",
                                                 diff.ToString().c_str(), cover_radius.ToString().c_str(), delta.ToString().c_str());
    return false;
  }
  BigRat c = FloorTo(diff, BigInt(1000000000LL));
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt(1000000000000LL));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt(1000000000000000LL));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = FloorTo(diff, BigInt("1000000000000000000000000000000"));
  }
  if (c <= BigRat(0)) {
    c = diff / BigRat(2);
  }
  if (c <= BigRat(0)) {
    if (fail_reason) *fail_reason = StringPrintf("c <= 0 after high precision floor (diff=%s)",
                                                 diff.ToString().c_str());
    return false;
  }

  BigRat scale = (c + delta) * BigRat(7, 4);
  for (int axis = 0; axis < 3; axis++) {
    for (int sign : {-1, 1}) {
      BigVecQ3 target(axis == 0 ? scale * BigRat(sign) : BigRat(0),
                   axis == 1 ? scale * BigRat(sign) : BigRat(0),
                   axis == 2 ? scale * BigRat(sign) : BigRat(0));
      BigRat lam[4];
      if (!Barycentric4(centers, target, lam)) {
        if (fail_reason) *fail_reason = "Barycentric4 degenerate";
        return false;
      }
      for (int i = 0; i < 4; i++) {
        if (lam[i] < 0) {
          if (fail_reason) *fail_reason = StringPrintf("target axis %d sign %d not inside (lam[%d]=%s)",
                                                       axis, sign, i, lam[i].ToString().c_str());
          return false;
        }
      }
    }
  }

  BigRat certified_r(0);
  for (const auto &cand : CANDIDATE_RS) {
    if (cand * cand * (BigRat(1) + c * c) <= BigRat(4) * c * c) {
      certified_r = cand;
      break;
    }
  }
  if (certified_r <= BigRat(0) && c > BigRat(0)) {
    // Dynamic fallback: for any c in (0, 1), r = c/2 strictly satisfies:
    // r^2 (1 + c^2) = (c^2 / 4) * (1 + c^2) <= c^2 / 2 < 4 * c^2.
    BigRat cand = c / BigRat(2);
    if (cand * cand * (BigRat(1) + c * c) <= BigRat(4) * c * c) {
      certified_r = cand;
    }
  }
  if (certified_r <= BigRat(0)) {
    if (fail_reason) *fail_reason = "No candidate radius satisfies angle bound";
    return false;
  }

  out_cert->c = c;
  out_cert->delta = delta;
  out_cert->r = certified_r;
  return true;
}

// ============================================================================
// CANDIDATE GENERATION, WOLFE SOLVER, AND UPPER BOUND ESTIMATION
// ============================================================================

using CandidateTriple = Tube229::CandidateTriple;


static void GenerateCandidatesForView(
    const vec3 &view,
    const TriangleQ &tri,
    bool evaluate_over_triangle,
    int cone_samples,
    bool include_boundaries,
    double screen_support_error,
    std::vector<CandidateTriple> *out_candidates) {
  *out_candidates = Tube229::GenerateCandidatesForView(
      view, tri, evaluate_over_triangle, cone_samples, include_boundaries, screen_support_error);
}

static bool SolveLinear4D(const double A[4][4], const double b[4], double x[4]) {
  double aug[4][5];
  for (int r = 0; r < 4; r++) {
    for (int c = 0; c < 4; c++) aug[r][c] = A[r][c];
    aug[r][4] = b[r];
  }
  for (int col = 0; col < 4; col++) {
    int pivot = col;
    double max_val = std::abs(aug[col][col]);
    for (int r = col + 1; r < 4; r++) {
      if (std::abs(aug[r][col]) > max_val) {
        max_val = std::abs(aug[r][col]);
        pivot = r;
      }
    }
    if (max_val < 1e-12) return false;
    if (pivot != col) {
      for (int c = 0; c < 5; c++) std::swap(aug[col][c], aug[pivot][c]);
    }
    double div = aug[col][col];
    for (int c = 0; c < 5; c++) aug[col][c] /= div;
    for (int r = 0; r < 4; r++) {
      if (r == col) continue;
      double mult = aug[r][col];
      for (int c = 0; c < 5; c++) aug[r][c] -= mult * aug[col][c];
    }
  }
  for (int r = 0; r < 4; r++) x[r] = aug[r][4];
  return true;
}

static bool TetrahedronOriginMargin(const vec3 pts[4], double *margin, double bary[4]) {
  double A[4][4];
  for (int col = 0; col < 4; col++) {
    A[0][col] = pts[col].x;
    A[1][col] = pts[col].y;
    A[2][col] = pts[col].z;
    A[3][col] = 1.0;
  }
  double b[4] = {0.0, 0.0, 0.0, 1.0};
  if (!SolveLinear4D(A, b, bary)) return false;
  if (bary[0] <= 1e-10 || bary[1] <= 1e-10 || bary[2] <= 1e-10 || bary[3] <= 1e-10) return false;

  double min_face_dist = 1e30;
  for (int omitted = 0; omitted < 4; omitted++) {
    vec3 face[3];
    int idx = 0;
    for (int i = 0; i < 4; i++) {
      if (i != omitted) face[idx++] = pts[i];
    }
    vec3 normal = yocto::cross(face[1] - face[0], face[2] - face[0]);
    double len = yocto::length(normal);
    if (len < 1e-12) return false;
    double d = std::abs(yocto::dot(normal, face[0])) / len;
    min_face_dist = std::min(min_face_dist, d);
  }
  *margin = min_face_dist;
  return true;
}

struct ClosestResult {
  double key = 1e30;
  std::vector<int> support;
  vec3 point = {0, 0, 0};
};

static ClosestResult ClosestOriginFace(const std::vector<vec3> &pts, const std::vector<int> &indices) {
  ClosestResult best{1e30, {}, {0, 0, 0}};

  auto consider = [&](const std::vector<int> &supp, const std::vector<double> &coeffs) {
    vec3 pt = {0, 0, 0};
    for (size_t i = 0; i < supp.size(); i++) {
      pt = pt + pts[supp[i]] * coeffs[i];
    }
    double k = yocto::dot(pt, pt);
    if (k < best.key) {
      best = {k, supp, pt};
    }
  };

  for (int idx : indices) consider({idx}, {1.0});

  int m = indices.size();
  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      int idx_a = indices[i], idx_b = indices[j];
      vec3 a = pts[idx_a], b = pts[idx_b];
      vec3 dir = b - a;
      double den = yocto::dot(dir, dir);
      if (den <= 1e-30) continue;
      double t = -yocto::dot(a, dir) / den;
      if (t > 1e-12 && t < 1.0 - 1e-12) {
        consider({idx_a, idx_b}, {1.0 - t, t});
      }
    }
  }

  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      for (int k = j + 1; k < m; k++) {
        int idx_a = indices[i], idx_b = indices[j], idx_c = indices[k];
        vec3 a = pts[idx_a], b = pts[idx_b], c = pts[idx_c];
        vec3 u = b - a;
        vec3 v = c - a;
        double uu = yocto::dot(u, u), uv = yocto::dot(u, v), vv = yocto::dot(v, v);
        double det = uu * vv - uv * uv;
        if (det <= 1e-30) continue;
        double au = yocto::dot(a, u), av = yocto::dot(a, v);
        double s = (-au * vv + av * uv) / det;
        double t = (-av * uu + au * uv) / det;
        if (s > 1e-12 && t > 1e-12 && (s + t) < 1.0 - 1e-12) {
          consider({idx_a, idx_b, idx_c}, {1.0 - s - t, s, t});
        }
      }
    }
  }
  return best;
}

static bool FindExtremalTetrahedron(const std::vector<vec3> &pts, std::array<int, 4> *out_indices) {
  int n = pts.size();
  if (n < 4) return false;
  const double inv_sqrt3 = 1.0 / std::sqrt(3.0);
  const vec3 base_t[4] = {
    { inv_sqrt3,  inv_sqrt3,  inv_sqrt3},
    { inv_sqrt3, -inv_sqrt3, -inv_sqrt3},
    {-inv_sqrt3,  inv_sqrt3, -inv_sqrt3},
    {-inv_sqrt3, -inv_sqrt3,  inv_sqrt3}
  };

  std::mt19937 rng(12345);
  std::normal_distribution<double> gauss(0.0, 1.0);

  for (int trial = 0; trial < 400; trial++) {
    vec3 v0 = {gauss(rng), gauss(rng), gauss(rng)};
    double l0 = yocto::length(v0);
    if (l0 < 1e-6) continue;
    v0 = v0 / l0;

    vec3 v1 = {gauss(rng), gauss(rng), gauss(rng)};
    v1 = v1 - v0 * yocto::dot(v0, v1);
    double l1 = yocto::length(v1);
    if (l1 < 1e-6) continue;
    v1 = v1 / l1;

    vec3 v2 = yocto::cross(v0, v1);

    vec3 u[4];
    for (int k = 0; k < 4; k++) {
      u[k] = v0 * base_t[k].x + v1 * base_t[k].y + v2 * base_t[k].z;
    }

    int idx[4];
    bool dup = false;
    for (int k = 0; k < 4; k++) {
      double max_dot = -1e30;
      int best_i = -1;
      for (int i = 0; i < n; i++) {
        double d = yocto::dot(pts[i], u[k]);
        if (d > max_dot) { max_dot = d; best_i = i; }
      }
      idx[k] = best_i;
      for (int prev = 0; prev < k; prev++) {
        if (idx[prev] == best_i) { dup = true; break; }
      }
      if (dup) break;
    }
    if (dup) continue;

    vec3 tpts[4] = {pts[idx[0]], pts[idx[1]], pts[idx[2]], pts[idx[3]]};
    double margin;
    double bary[4];
    if (TetrahedronOriginMargin(tpts, &margin, bary)) {
      *out_indices = {idx[0], idx[1], idx[2], idx[3]};
      return true;
    }
  }
  return false;
}

static void EstimateUpperBounds(
    const TriangleQ &tri,
    const std::vector<vec3> &pts,
    BigRat *out_c_upper,
    BigRat *out_r_upper) {

  if (pts.empty()) {
    *out_c_upper = BigRat(0);
    *out_r_upper = BigRat(0);
    return;
  }

  double min_support = 1e30;
  std::mt19937 rng(42);
  std::normal_distribution<double> gauss(0.0, 1.0);
  vec3 worst_u = {0, 0, 0};
  for (int s = 0; s < 1500; s++) {
    vec3 u = {gauss(rng), gauss(rng), gauss(rng)};
    double len = yocto::length(u);
    if (len < 1e-12) continue;
    u = u / len;
    double max_dot = -1e30;
    for (const auto &p : pts) max_dot = std::max(max_dot, yocto::dot(u, p));
    if (max_dot < min_support) {
      min_support = max_dot;
      worst_u = u;
    }
  }
  for (int step = 0; step < 500; step++) {
    vec3 pert = {gauss(rng) * 0.05, gauss(rng) * 0.05, gauss(rng) * 0.05};
    vec3 u = worst_u + pert;
    double len = yocto::length(u);
    if (len < 1e-12) continue;
    u = u / len;
    double max_dot = -1e30;
    for (const auto &p : pts) max_dot = std::max(max_dot, yocto::dot(u, p));
    if (max_dot < min_support) {
      min_support = max_dot;
      worst_u = u;
    }
  }

  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  double diam = std::max({yocto::length(c0 - c1), yocto::length(c1 - c2), yocto::length(c2 - c0)});

  // c_max <= 0.542857 * max(0, min_support) + 0.52 * diam
  double c_max_d = 0.542857 * std::max(0.0, min_support) + 0.52 * diam;
  if (c_max_d < 0.0) c_max_d = 0.0;

  double r_max_d = (c_max_d < 0.99) ? (2.0 * c_max_d / std::sqrt(1.0 - c_max_d * c_max_d)) : 2.0;

  int64_t c_int = static_cast<int64_t>(std::ceil(c_max_d * 100000000.0));
  *out_c_upper = BigRat(c_int, 100000000LL);

  int64_t r_int = static_cast<int64_t>(std::ceil(r_max_d * 100000000.0));
  *out_r_upper = BigRat(r_int, 100000000LL);
}

// ----------------------------------------------------------------------------
// Thread-safe Certificate Cache
// ----------------------------------------------------------------------------

class CertificateCache {
 public:
  void Insert(const TubeCertificate &cert) {
    std::lock_guard<std::mutex> lock(mu_);
    cache_.push_back(cert);
    if (cache_.size() > 500) {
      cache_.erase(cache_.begin(), cache_.begin() + 100);
    }
  }

  std::vector<TubeCertificate> GetRecent() const {
    std::lock_guard<std::mutex> lock(mu_);
    return cache_;
  }

  std::vector<TubeCertificate> GetLastN(int n) const {
    std::lock_guard<std::mutex> lock(mu_);
    int sz = cache_.size();
    int count = std::min(sz, n);
    std::vector<TubeCertificate> result;
    result.reserve(count);
    for (int i = sz - count; i < sz; i++) {
      result.push_back(cache_[i]);
    }
    return result;
  }

 private:
  mutable std::mutex mu_;
  std::vector<TubeCertificate> cache_;
};

static bool SynthesizeCertificate(
    const TriangleQ &tri,
    int depth,
    const BigRat &target_c,
    const BigRat &target_r,
    TubeCertificate *out_cert,
    const std::vector<ContactInfo> &extra_contacts = {},
    const std::vector<Tube229::CandidateTriple> &extra_axes = {},
    bool fast_pass = false) {

  // Delegate directly to Tube229::SynthesizeCertificate, which runs
  // fast single-view centroid synthesis first and escalates to multi-view
  // iterative cutting-plane opposing search if needed.
  if (Tube229::SynthesizeCertificate(
          tri, depth, out_cert, extra_contacts, extra_axes, /*fast_only=*/fast_pass)) {
    if (out_cert->r > BigRat(0) && out_cert->c > BigRat(0) &&
        (target_r <= BigRat(0) || out_cert->r >= target_r) &&
        (target_c <= BigRat(0) || out_cert->c >= target_c)) {
      return true;
    }
  }

  return false;
}

// ============================================================================
// INCREMENTAL BFS TUBE SEARCH MANAGER
// ============================================================================

static bool TryCertifyNode(
    const TriangleQ &tri,
    int depth,
    const BigRat &target_c,
    const BigRat &target_r,
    const CertificateCache &cache,
    TubeCertificate *out_cert,
    bool fast_pass = false) {

  // 1. Audit existing cache or synthesize direct certificate
  std::vector<TubeCertificate> all_recent = cache.GetLastN(20);
  for (int i = (int)all_recent.size() - 1; i >= 0; i--) {
    if (AuditCertificateAdaptive(tri, all_recent[i], out_cert)) {
      if (out_cert->r > BigRat(0) && out_cert->c > BigRat(0) &&
          (target_r <= BigRat(0) || out_cert->r >= target_r) &&
          (target_c <= BigRat(0) || out_cert->c >= target_c)) {
        return true;
      }
    }
  }

  // 1b. Axis Recombination from recent certificates
  std::vector<ContactInfo> extra_contacts;
  auto add_contact = [&](const ContactInfo &c) {
    for (const auto &ex : extra_contacts) {
      if (ex.vertex == c.vertex &&
          ex.edge_start == c.edge_start &&
          ex.edge_finish == c.edge_finish &&
          ex.edge_start2 == c.edge_start2 &&
          ex.edge_finish2 == c.edge_finish2 &&
          ex.mix == c.mix) {
        return;
      }
    }
    extra_contacts.push_back(c);
  };

  int n_recomb = std::min((int)all_recent.size(), 15);
  for (int i = (int)all_recent.size() - 1; i >= (int)all_recent.size() - n_recomb; i--) {
    for (int a = 0; a < 4; a++) {
      for (int m = 0; m < 3; m++) {
        add_contact(all_recent[i].axes[a].contacts[m]);
      }
    }
  }

  std::vector<Tube229::CandidateTriple> valid_axes;
  if (!all_recent.empty()) {
    for (int i = (int)all_recent.size() - 1; i >= (int)all_recent.size() - n_recomb; i--) {
      const auto &rc = all_recent[i];
      for (int a = 0; a < 4; a++) {
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri, rc.axes[a].contacts, &cand)) {
          bool dup = false;
          for (const auto &ex : valid_axes) {
            if (yocto::length(ex.normalized_a - cand.normalized_a) < 1e-6) {
              dup = true; break;
            }
          }
          if (!dup) valid_axes.push_back(cand);
        }
      }
    }
    if (valid_axes.size() >= 4) {
      std::array<int, 4> simplex;
      if (Tube229::FindBalancedTetrahedron(valid_axes, &simplex)) {
        TubeCertificate recomb_cert;
        for (int a = 0; a < 4; a++) {
          recomb_cert.axes[a].contacts[0] = valid_axes[simplex[a]].contacts[0];
          recomb_cert.axes[a].contacts[1] = valid_axes[simplex[a]].contacts[1];
          recomb_cert.axes[a].contacts[2] = valid_axes[simplex[a]].contacts[2];
        }
        if (AuditCertificateAdaptive(tri, recomb_cert, out_cert)) {
          if (out_cert->r > BigRat(0) && out_cert->c > BigRat(0) &&
              (target_r <= BigRat(0) || out_cert->r >= target_r) &&
              (target_c <= BigRat(0) || out_cert->c >= target_c)) {
            return true;
          }
        }
      }
    }
  }

  if (SynthesizeCertificate(tri, depth, target_c, target_r, out_cert, extra_contacts, valid_axes, fast_pass)) {
    if (out_cert->r > BigRat(0) && out_cert->c > BigRat(0) &&
        (target_r <= BigRat(0) || out_cert->r >= target_r) &&
        (target_c <= BigRat(0) || out_cert->c >= target_c)) {
      return true;
    }
  }

  return false;
}


class IncrementalTubeManager {
 public:
  IncrementalTubeManager(
      std::string root_path,
      int max_depth,
      BigRat target_r,
      BigRat target_c,
      int num_workers,
      std::string output_dir,
      bool revalidate = false)
      : root_path_(std::move(root_path)),
        max_depth_(max_depth),
        target_r_(std::move(target_r)),
        target_c_(std::move(target_c)),
        num_workers_(num_workers),
        output_dir_(std::move(output_dir)),
        revalidate_(revalidate) {

    std::filesystem::create_directories(output_dir_);
  }

  void set_checkpoint_minutes(int m) { checkpoint_minutes_ = m; }

  static double SphericalArea(vec3 a, vec3 b, vec3 c) {
    a = a / yocto::length(a);
    b = b / yocto::length(b);
    c = c / yocto::length(c);
    double num = std::abs(yocto::dot(a, yocto::cross(b, c)));
    double den = 1.0 + yocto::dot(a, b) + yocto::dot(b, c) + yocto::dot(c, a);
    return 2.0 * std::atan2(num, den);
  }

  void ComputeAndPrintCoverage() const {
    if (!root_) return;
    TriangleQ root_tri = root_->GetTriangle();
    vec3 r0 = ToDouble(root_tri.corners[0]);
    vec3 r1 = ToDouble(root_tri.corners[1]);
    vec3 r2 = ToDouble(root_tri.corners[2]);
    double total_area = SphericalArea(r0, r1, r2);

    double covered_area = 0.0;
    int covered_regions = 0;
    int uncertified_leaves = 0;

    auto traverse = [&](auto &self, const TreeNode* n) -> bool {
      if (n->direct_cert.has_value() && n->direct_cert->r > BigRat(0)) {
        TriangleQ tri = n->GetTriangle();
        vec3 v0 = ToDouble(tri.corners[0]);
        vec3 v1 = ToDouble(tri.corners[1]);
        vec3 v2 = ToDouble(tri.corners[2]);
        covered_area += SphericalArea(v0, v1, v2);
        covered_regions++;
        return true;
      }
      if (n->children.size() == 4) {
        bool all_covered = true;
        for (int i = 0; i < 4; i++) {
          if (!self(self, n->children[i].get())) {
            all_covered = false;
          }
        }
        return all_covered;
      }
      uncertified_leaves++;
      return false;
    };

    traverse(traverse, root_.get());
    double pct = (covered_area / total_area) * 100.0;
    std::cout << std::fixed << std::setprecision(6);
    std::cout << "Tree Coverage: " << pct << "% (" << covered_area << " / " << total_area << " sr)\n"
              << "Uncovered Area: " << (total_area - covered_area) << " sr (" << (100.0 - pct) << "%)\n"
              << "Certified Regions: " << covered_regions << "\n"
              << "Uncertified Leaves: " << uncertified_leaves << "\n\n" << std::flush;
  }

  void RunAncestorSweep(int min_depth, int max_depth) {
    std::string main_file = SubtreeFilename(root_path_, output_dir_);
    if (!std::filesystem::exists(main_file)) {
      std::cerr << "Cannot run ancestor sweep: file not found: " << main_file << "\n";
      return;
    }
    std::cout << ACYAN("Loading tree from ") << main_file << "...\n";
    root_ = LoadTreeJson(main_file, /*load_external=*/false, output_dir_);
    if (!root_) {
      std::cerr << "Failed to load root tree.\n";
      return;
    }

    std::cout << ACYAN("Initial Tree Status before Ancestor Sweep:\n");
    ComputeAndPrintCoverage();

    auto populate_cache = [&](auto &self, TreeNode *node) -> void {
      if (!node) return;
      if (node->direct_cert.has_value() && node->direct_cert->r > BigRat(0)) {
        cache_.Insert(*node->direct_cert);
      }
      for (auto &c : node->children) self(self, c.get());
    };
    populate_cache(populate_cache, root_.get());

    std::cout << ACYAN("Starting Ancestor Sweep on ") << num_workers_ << " threads\n"
              << "Depths: " << min_depth << " to " << max_depth << "\n"
              << "Subdivision: DISABLED (pure pruning/certification pass)\n\n" << std::flush;

    auto has_uncertified_descendants = [](auto &self, const TreeNode *node) -> bool {
      if (!node) return false;
      if (node->direct_cert.has_value() && node->direct_cert->r > BigRat(0)) {
        return false;
      }
      if (node->children.empty()) {
        return true;
      }
      for (const auto &c : node->children) {
        if (self(self, c.get())) return true;
      }
      return false;
    };

    int total_nodes_certified = 0;
    int total_leaves_pruned = 0;
    int total_leaves_upgraded = 0;
    int total_subtrees_preserved = 0;

    for (int d = min_depth; d <= max_depth; d++) {
      std::vector<TreeNode*> target_nodes;
      auto collect_depth = [&](auto &self, TreeNode *node) -> void {
        if (!node) return;
        if (node->direct_cert.has_value() && node->direct_cert->r > BigRat(0)) {
          return;
        }
        if (node->depth() == d) {
          if (node->children.empty() || has_uncertified_descendants(has_uncertified_descendants, node)) {
            target_nodes.push_back(node);
          }
          return;
        }
        for (auto &c : node->children) {
          self(self, c.get());
        }
      };
      collect_depth(collect_depth, root_.get());

      if (target_nodes.empty()) {
        std::cout << "Depth " << d << ": 0 uncertified candidate nodes.\n" << std::flush;
        continue;
      }

      std::cout << ACYAN("Depth ") << d << ": " << target_nodes.size() << " uncertified nodes to test...\n" << std::flush;

      std::atomic<size_t> next_idx{0};
      std::atomic<size_t> completed_cnt{0};
      std::mutex result_mu;
      std::vector<std::pair<TreeNode*, TubeCertificate>> newly_certified;
      auto start_time = std::chrono::steady_clock::now();

      auto sweep_worker = [&]() {
        while (!g_stop_requested) {
          size_t idx = next_idx.fetch_add(1);
          if (idx >= target_nodes.size()) break;
          TreeNode *node = target_nodes[idx];
          TriangleQ tri = node->GetTriangle();

          if (target_nodes.size() <= 50) {
            std::cout << "Testing node " << node->path << " (depth " << node->depth() << ")...\n" << std::flush;
          }

          TubeCertificate cert;
          bool certified = TryCertifyNode(tri, node->depth(), target_c_, target_r_, cache_, &cert, /*fast_pass=*/true);
          if (!certified) {
            certified = TryCertifyNode(tri, node->depth(), target_c_, target_r_, cache_, &cert, /*fast_pass=*/false);
          }
          if (certified) {
            std::lock_guard<std::mutex> lock(result_mu);
            newly_certified.push_back({node, cert});
            node->direct_cert = cert;
            cache_.Insert(cert);
            if (node->direct_bounds.direct_r_lower == BigRat(0) || cert.r < node->direct_bounds.direct_r_lower) {
              node->direct_bounds.direct_r_lower = cert.r;
            }
            if (node->direct_bounds.direct_c_lower == BigRat(0) || cert.c < node->direct_bounds.direct_c_lower) {
              node->direct_bounds.direct_c_lower = cert.c;
            }
            std::cout << AGREEN("  SUCCESS on node ") << node->path
                      << ": c = " << cert.c.ToString() << " (" << cert.c.ToDouble() << ")"
                      << ", r = " << cert.r.ToString() << " (" << cert.r.ToDouble() << ")\n" << std::flush;
          } else {
            if (target_nodes.size() <= 50) {
              std::cout << ARED("  FAILED on node ") << node->path << "\n" << std::flush;
            }
          }
          size_t done = completed_cnt.fetch_add(1) + 1;
          size_t print_interval = std::min((size_t)250, std::max((size_t)1, target_nodes.size() / 20));
          if (done % print_interval == 0 || done == target_nodes.size()) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - start_time).count();
            double rate = elapsed > 0 ? (done / elapsed) : 0;
            std::cout << "[Depth " << d << "] Tested " << done << " / " << target_nodes.size()
                      << " (" << (done * 100 / target_nodes.size()) << "%) | Certified: " << newly_certified.size()
                      << " | Rate: " << std::fixed << std::setprecision(1) << rate << " nodes/s\n" << std::flush;
          }
        }
      };

      std::vector<std::thread> workers;
      for (int t = 0; t < num_workers_; t++) {
        workers.emplace_back(sweep_worker);
      }
      for (auto &w : workers) {
        w.join();
      }

      int upgraded_this_depth = 0;
      int subtrees_preserved_this_depth = 0;

      for (auto &[node, cert] : newly_certified) {
        node->direct_cert = cert;
        node->direct_bounds.direct_r_lower = cert.r;
        node->direct_bounds.direct_c_lower = cert.c;
        cache_.Insert(cert);

        if (!node->children.empty()) {
          // Preserve all descendant leaves; do not discard them!
          subtrees_preserved_this_depth++;
          auto propagate_cert = [&](auto &self, TreeNode *n) -> void {
            if (n->children.empty()) {
              if (!n->direct_cert.has_value() || n->direct_cert->r < cert.r) {
                n->direct_cert = cert;
                n->direct_bounds.direct_r_lower = cert.r;
                n->direct_bounds.direct_c_lower = cert.c;
                upgraded_this_depth++;
              }
              return;
            }
            for (auto &c : n->children) {
              self(self, c.get());
            }
          };
          propagate_cert(propagate_cert, node);
        } else {
          upgraded_this_depth++;
        }
      }

      total_nodes_certified += newly_certified.size();
      total_leaves_upgraded += upgraded_this_depth;
      total_subtrees_preserved += subtrees_preserved_this_depth;

      std::cout << "Depth " << d << " results: " << newly_certified.size() << " certified ancestors, "
                << subtrees_preserved_this_depth << " subtrees preserved with better/upgraded bounds ("
                << upgraded_this_depth << " uncertified/worse leaves upgraded)!\n" << std::flush;

      if (!newly_certified.empty()) {
        std::cout << ACYAN("Saving updated tree to ") << main_file << "...\n" << std::flush;
        SaveTreeJson(*root_, main_file, /*shallow=*/false);
      }
    }

    std::cout << "\n" << AGREEN("=== Ancestor Sweep Finished ===") << "\n"
              << "Total Nodes Certified:    " << total_nodes_certified << "\n"
              << "Total Leaves Pruned:      " << total_leaves_pruned << "\n"
              << "Total Leaves Upgraded:    " << total_leaves_upgraded << "\n"
              << "Total Subtrees Preserved: " << total_subtrees_preserved << "\n\n" << std::flush;

    ComputeAndPrintCoverage();
  }

  void RunLeafSweep(int min_depth, int max_depth) {
    std::string main_file = SubtreeFilename(root_path_, output_dir_);
    if (!std::filesystem::exists(main_file)) {
      std::cerr << "Cannot run leaf sweep: file not found: " << main_file << "\n";
      return;
    }
    std::cout << ACYAN("Loading tree from ") << main_file << "...\n";
    root_ = LoadTreeJson(main_file, /*load_external=*/false, output_dir_);
    if (!root_) {
      std::cerr << "Failed to load root tree.\n";
      return;
    }

    std::cout << ACYAN("Initial Tree Status before Leaf Sweep:\n");
    ComputeAndPrintCoverage();

    auto populate_cache = [&](auto &self, TreeNode *node) -> void {
      if (!node) return;
      if (node->direct_cert.has_value() && node->direct_cert->r > BigRat(0)) {
        cache_.Insert(*node->direct_cert);
      }
      for (auto &c : node->children) self(self, c.get());
    };
    populate_cache(populate_cache, root_.get());

    std::cout << ACYAN("Starting Leaf Sweep on ") << num_workers_ << " threads\n"
              << "Depths: " << min_depth << " to " << max_depth << "\n"
              << "Subdivision: DISABLED (pure certification pass on uncertified leaves)\n\n" << std::flush;

    int total_leaves_tested = 0;
    int total_leaves_certified = 0;
    int total_leaves_failed = 0;

    int step = (min_depth <= max_depth) ? 1 : -1;
    for (int d = min_depth; (step > 0 ? d <= max_depth : d >= max_depth); d += step) {
      if (g_stop_requested) break;

      std::vector<TreeNode*> target_leaves;
      auto collect_depth = [&](auto &self, TreeNode *node) -> void {
        if (!node) return;
        if (node->children.empty()) {
          if (node->depth() == d) {
            bool has_valid_cert = false;
            if (node->direct_cert.has_value()) {
              bool positive = (node->direct_cert->r > BigRat(0) && node->direct_cert->c > BigRat(0));
              bool meets_r = (target_r_ <= BigRat(0)) || (node->direct_cert->r >= target_r_);
              bool meets_c = (target_c_ <= BigRat(0)) || (node->direct_cert->c >= target_c_);
              has_valid_cert = positive && meets_r && meets_c;
            }
            if (!has_valid_cert && !node->external) {
              target_leaves.push_back(node);
            }
          }
          return;
        }
        for (auto &c : node->children) {
          self(self, c.get());
        }
      };
      collect_depth(collect_depth, root_.get());

      if (target_leaves.empty()) {
        std::cout << "Depth " << d << ": 0 uncertified leaves to test.\n" << std::flush;
        continue;
      }

      std::cout << ACYAN("Depth ") << d << ": " << target_leaves.size() << " uncertified leaves to test...\n" << std::flush;
      std::cout << "First 5 target leaves:\n";
      for (size_t i = 0; i < std::min((size_t)5, target_leaves.size()); i++) {
        std::cout << "  " << target_leaves[i]->path << "\n";
      }
      std::cout << std::flush;

      std::atomic<size_t> next_idx{0};
      std::atomic<size_t> completed_cnt{0};
      std::atomic<size_t> depth_certified{0};
      std::atomic<size_t> depth_failed{0};
      std::mutex tree_mu;
      auto start_time = std::chrono::steady_clock::now();
      auto last_save_time = std::chrono::steady_clock::now();
      const double checkpoint_seconds = checkpoint_minutes_ * 60.0;
      std::atomic<size_t> last_saved_count{0};

      auto worker = [&]() {
        while (!g_stop_requested) {
          size_t idx = next_idx.fetch_add(1);
          if (idx >= target_leaves.size()) break;
          TreeNode *node = target_leaves[idx];
          TriangleQ tri = node->GetTriangle();

          TubeCertificate cert;
          if (TryCertifyNode(tri, node->depth(), target_c_, target_r_, cache_, &cert, /*fast_pass=*/true)) {
            std::lock_guard<std::mutex> lock(tree_mu);
            node->direct_cert = cert;
            node->direct_bounds.direct_r_lower = cert.r;
            node->direct_bounds.direct_c_lower = cert.c;
            cache_.Insert(cert);
            depth_certified++;
          } else {
            depth_failed++;
          }

          size_t done = completed_cnt.fetch_add(1) + 1;
          if (done % 500 == 0 || done == target_leaves.size()) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - start_time).count();
            double rate = elapsed > 0 ? (done / elapsed) : 0;
            std::cout << "[" << d << "] Tested: " << done << " / " << target_leaves.size()
                      << " | Cert: " << depth_certified.load()
                      << " | Fail: " << depth_failed.load()
                      << " | Rate: " << std::fixed << std::setprecision(1) << rate << " leaves/s\n" << std::flush;
          }

          // Wall-time periodic checkpoint (every checkpoint_minutes) if new certificates were found
          if (done % 500 == 0) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - last_save_time).count();
            if (elapsed >= checkpoint_seconds && depth_certified.load() > last_saved_count.load()) {
              std::lock_guard<std::mutex> lock(tree_mu);
              elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - last_save_time).count();
              if (elapsed >= checkpoint_seconds && depth_certified.load() > last_saved_count.load()) {
                last_save_time = std::chrono::steady_clock::now();
                last_saved_count = depth_certified.load();
                std::cout << ACYAN("\n[CHECKPOINT] Periodic wall-time save (") << static_cast<int>(elapsed / 60.0)
                          << "m elapsed) with " << depth_certified.load() << " certified leaves to " << main_file << "...\n" << std::flush;
                SaveTreeJson(*root_, main_file, /*shallow=*/false);
              }
            }
          }
        }
      };

      std::vector<std::thread> threads;
      threads.reserve(num_workers_);
      for (int i = 0; i < num_workers_; i++) {
        threads.emplace_back(worker);
      }
      for (auto &t : threads) {
        if (t.joinable()) t.join();
      }

      total_leaves_tested += target_leaves.size();
      total_leaves_certified += depth_certified.load();
      total_leaves_failed += depth_failed.load();

      std::cout << "Depth " << d << " results: Tested " << target_leaves.size()
                << " | Certified: " << depth_certified.load()
                << " | Failed: " << depth_failed.load() << "\n" << std::flush;

      if (depth_certified.load() > 0) {
        std::cout << ACYAN("Saving updated tree after depth ") << d << " to " << main_file << "...\n" << std::flush;
        SaveTreeJson(*root_, main_file, /*shallow=*/false);
      }
    }

    std::cout << "\n" << AGREEN("=== Leaf Sweep Finished ===") << "\n"
              << "Total Leaves Tested:    " << total_leaves_tested << "\n"
              << "Total Leaves Certified: " << total_leaves_certified << "\n"
              << "Total Leaves Failed:    " << total_leaves_failed << "\n\n" << std::flush;

    ComputeAndPrintCoverage();
  }

  void Run() {

    std::string main_file = SubtreeFilename(root_path_, output_dir_);

    if (std::filesystem::exists(main_file)) {
      std::cout << ACYAN("Resuming tree from ") << main_file << "...\n";
      root_ = LoadTreeJson(main_file, /*load_external=*/false, output_dir_);
      if (revalidate_ && root_) {
        std::cout << ACYAN("Revalidating existing certificates across tree...\n");
        int kept = 0, discarded = 0;
        auto reval = [&](auto &self, TreeNode *node) -> void {
          if (!node) return;
          if (node->direct_cert.has_value()) {
            TriangleQ tri = node->GetTriangle();
            TubeCertificate audited;
            if (AuditCertificateAdaptive(tri, *node->direct_cert, &audited)) {
              node->direct_cert = audited;
              node->direct_bounds.direct_r_lower = audited.r;
              node->direct_bounds.direct_c_lower = audited.c;
              cache_.Insert(audited);
              kept++;
            } else {
              node->direct_cert.reset();
              node->direct_bounds.direct_r_lower = BigRat(0);
              node->direct_bounds.direct_c_lower = BigRat(0);
              discarded++;
            }
          }
          for (auto &c : node->children) {
            self(self, c.get());
          }
        };
        reval(reval, root_.get());
        std::cout << "Revalidation finished: kept " << kept << " valid certs, invalidated "
                  << discarded << " stale certs.\n";
        if (discarded > 0) {
          std::cout << ACYAN("Saving revalidated tree to ") << main_file << "...\n";
          SaveTreeJson(*root_, main_file, /*shallow=*/false);
        }
      }
    }

    if (!root_) {
      root_ = std::make_unique<TreeNode>();
      root_->path = root_path_;
    }

    std::unordered_map<std::string, TreeNode*> node_map;

    // Prioritized queue: process shallower nodes first (depth-stratified buckets).
    // Within each depth bucket, nodes are processed in FIFO order.
    static constexpr int kMaxDepthBuckets = 64;
    std::array<std::deque<std::string>, kMaxDepthBuckets> queues_by_depth;
    size_t total_queue_size = 0;

    auto push_queue = [&](const std::string &p) {
      int d = std::clamp(static_cast<int>(p.size()), 0, kMaxDepthBuckets - 1);
      queues_by_depth[d].push_back(p);
      total_queue_size++;
    };

    auto pop_queue = [&]() -> std::string {
      for (int d = 0; d < kMaxDepthBuckets; d++) {
        if (!queues_by_depth[d].empty()) {
          std::string p = std::move(queues_by_depth[d].front());
          queues_by_depth[d].pop_front();
          total_queue_size--;
          return p;
        }
      }
      return "";
    };

    auto queue_empty = [&]() -> bool {
      return total_queue_size == 0;
    };

    auto collect_nodes = [&](auto &self, TreeNode *node) -> void {
      if (!node) return;
      node_map[node->path] = node;
      if (node->direct_cert.has_value()) {
        cache_.Insert(*node->direct_cert);
      }
      if (node->children.empty() && !node->external) {
        bool target_achieved = false;
        if (node->direct_cert.has_value()) {
          bool positive = (node->direct_cert->r > BigRat(0) && node->direct_cert->c > BigRat(0));
          bool meets_r = (target_r_ <= BigRat(0)) || (node->direct_cert->r >= target_r_);
          bool meets_c = (target_c_ <= BigRat(0)) || (node->direct_cert->c >= target_c_);
          target_achieved = positive && meets_r && meets_c;
        }
        bool infeasible = false;
        if (target_r_ > BigRat(0) && node->direct_bounds.direct_r_upper > BigRat(0) &&
            node->direct_bounds.direct_r_upper < target_r_) {
          infeasible = true;
        }
        if (target_c_ > BigRat(0) && node->direct_bounds.direct_c_upper > BigRat(0) &&
            node->direct_bounds.direct_c_upper < target_c_) {
          infeasible = true;
        }
        if (!target_achieved && !infeasible) {
          push_queue(node->path);
        }
      } else {
        for (const auto &child : node->children) {
          self(self, child.get());
        }
      }
    };
    collect_nodes(collect_nodes, root_.get());

    if (queue_empty() && root_->children.empty()) {
      push_queue(root_->path);
    }

    std::cout << ACYAN("Starting Incremental BFS Tube Search on ") << num_workers_ << " threads\n"
              << "Root Path: \"" << root_path_ << "\"\n"
              << "Target Radius: " << target_r_.ToString() << "\n"
              << "Target Margin: " << target_c_.ToString() << "\n"
              << "Max Depth: " << max_depth_ << "\n"
              << "Initial Queue: " << total_queue_size << " nodes\n\n" << std::flush;

    std::mutex queue_mu;
    std::condition_variable cv;
    bool done = false;
    int busy_workers = 0;
    std::atomic<int64_t> total_processed{0};
    std::atomic<int64_t> count_target_met{0};
    std::atomic<int64_t> count_pruned{0};
    std::atomic<int64_t> count_subdivided{0};
    std::atomic<int64_t> count_capped{0};
    auto last_save_time = std::chrono::steady_clock::now();
    const double checkpoint_seconds = checkpoint_minutes_ * 60.0;

    auto worker_func = [&](int tid) {
      while (true) {
        std::string cur_path;
        TreeNode *node = nullptr;
        {
          std::unique_lock<std::mutex> lock(queue_mu);
          while (queue_empty() || g_stop_requested) {
            if (g_stop_requested) {
              done = true;
              cv.notify_all();
              return;
            }
            if (busy_workers == 0) {
              done = true;
              cv.notify_all();
              return;
            }
            cv.wait(lock);
            if (done || g_stop_requested) return;
          }
          cur_path = pop_queue();
          node = node_map[cur_path];
          busy_workers++;
        }

        if (!node) {
          std::lock_guard<std::mutex> lock(queue_mu);
          busy_workers--;
          continue;
        }
        TriangleQ tri = node->GetTriangle();

        bool meets_target = false;
        bool infeasible = false;

        // 1. Audit existing cache or synthesize direct certificate
        TubeCertificate cert;
        bool cert_found = TryCertifyNode(tri, node->depth(), target_c_, target_r_, cache_, &cert);

        if (cert_found) {
          node->direct_cert = cert;
          node->direct_bounds.direct_r_lower = cert.r;
          node->direct_bounds.direct_c_lower = cert.c;
          cache_.Insert(cert);
        }


        if (cert_found) {
          bool positive = (cert.r > BigRat(0) && cert.c > BigRat(0));
          bool meets_r = (target_r_ <= BigRat(0)) || (cert.r >= target_r_);
          bool meets_c = (target_c_ <= BigRat(0)) || (cert.c >= target_c_);
          meets_target = (positive && meets_r && meets_c);
        }

        // 2. If target not met, compute upper bounds and test for infeasibility
        infeasible = false;
        if (!meets_target) {
          if (node->direct_bounds.direct_c_upper <= BigRat(0) &&
              node->direct_bounds.direct_r_upper <= BigRat(0)) {
            vec3 centroid = (ToDouble(tri.corners[0]) +
                             ToDouble(tri.corners[1]) +
                             ToDouble(tri.corners[2])) / 3.0;
            std::vector<CandidateTriple> candidates;
            GenerateCandidatesForView(centroid, tri, /*evaluate_over_triangle=*/false, 4, true, 2e-14, &candidates);
            std::vector<vec3> pts;
            pts.reserve(candidates.size());
            for (const auto &c : candidates) pts.push_back(c.normalized_a);

            BigRat c_upper(0), r_upper(0);
            EstimateUpperBounds(tri, pts, &c_upper, &r_upper);
            node->direct_bounds.direct_c_upper = c_upper;
            node->direct_bounds.direct_r_upper = r_upper;
          }

          if (target_r_ > BigRat(0) && node->direct_bounds.direct_r_upper > BigRat(0) &&
              node->direct_bounds.direct_r_upper < target_r_) {
            infeasible = true;
          }
          if (target_c_ > BigRat(0) && node->direct_bounds.direct_c_upper > BigRat(0) &&
              node->direct_bounds.direct_c_upper < target_c_) {
            infeasible = true;
          }
        }

        // 3. Subdivision decision
        bool max_depth_reached = (node->depth() >= max_depth_);

        if (meets_target) {
          count_target_met++;
        } else if (infeasible) {
          count_pruned++;
        } else if (max_depth_reached) {
          // Cap depth splits: strictly enforce max_depth cap and do not split further.
          count_capped++;
        } else {
          // Subdivide!
          count_subdivided++;
          std::vector<std::string> new_paths;
          {
            std::lock_guard<std::mutex> lock(queue_mu);
            node->children.reserve(4);
            for (int i = 0; i < 4; i++) {
              auto child = std::make_unique<TreeNode>();
              child->path = cur_path + std::to_string(i);
              node_map[child->path] = child.get();
              new_paths.push_back(child->path);
              node->children.push_back(std::move(child));
            }
            for (const auto &np : new_paths) {
              push_queue(np);
            }
            cv.notify_all();
          }
        }

        // TODO(tom7): Idea 3 - Ancestor Pruning / Shallower Certificates:
        // When all 4 children of an internal node possess valid certificates (or when
        // a parent triangle is audited against recent certificates), verify if the parent
        // can be certified with r = min(child_r), allowing the 4 child nodes to be
        // pruned/coalesced to keep the tree compact and accelerate verification.

        int64_t processed = ++total_processed;
        if (processed % 100 == 0) {
          size_t q_size = 0;
          {
            std::lock_guard<std::mutex> lock(queue_mu);
            q_size = total_queue_size;
          }
          std::cout << std::format(
            "[{}] Processed: {} | Queue: {} | Met Target: {} | Pruned: {} | Subdivided: {} | Capped: {}\n",
            cur_path, processed, q_size, count_target_met.load(), count_pruned.load(), count_subdivided.load(), count_capped.load()
          ) << std::flush;
        }

        if (processed % 1000 == 0) {
          auto now = std::chrono::steady_clock::now();
          double elapsed = std::chrono::duration<double>(now - last_save_time).count();
          if (elapsed >= checkpoint_seconds) {
            std::lock_guard<std::mutex> lock(queue_mu);
            elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - last_save_time).count();
            if (elapsed >= checkpoint_seconds) {
              last_save_time = std::chrono::steady_clock::now();
              std::cout << ACYAN("\n[CHECKPOINT] Periodic wall-time save (") << static_cast<int>(elapsed / 60.0)
                        << "m elapsed) at " << processed << " nodes to " << main_file << "...\n" << std::flush;
              SaveTreeJson(*root_, main_file, /*shallow=*/false);
            }
          }
        }

        {
          std::lock_guard<std::mutex> lock(queue_mu);
          busy_workers--;
          if (queue_empty() && busy_workers == 0) {
            done = true;
            cv.notify_all();
            return;
          }
        }
      }
    };

    std::vector<std::thread> threads;
    for (int i = 0; i < num_workers_; i++) {
      threads.emplace_back(worker_func, i);
    }
    for (auto &t : threads) {
      if (t.joinable()) t.join();
    }

    if (g_stop_requested) {
      std::cout << ACYAN("\n[CHECKPOINT] Stop requested. Saving clean checkpoint before exiting...\n") << std::flush;
      SaveTreeJson(*root_, main_file, /*shallow=*/false);
      return;
    }

    // Final save
    SaveTreeJson(*root_, main_file, /*shallow=*/false);
    TreeStats stats = ComputeTreeStats(*root_);
    EffectiveBounds eb = ComputeEffectiveBounds(*root_);

    std::cout << "\n" << AGREEN("=== INCREMENTAL SEARCH COMPLETE ===") << "\n"
              << "Main Tree File: " << main_file << "\n"
              << "Total Nodes: " << stats.total_nodes << " (Leaves: " << stats.leaves
              << ", Direct Certs: " << stats.direct_certificates << ")\n"
              << "Max Depth: " << stats.max_depth << "\n"
              << "Root Effective r_lower: " << eb.r_lower.ToString() << "\n"
              << "Root Effective r_upper: " << eb.r_upper.ToString() << "\n"
              << "Complete Coverage: " << (eb.complete ? "YES" : "INCOMPLETE") << "\n\n";
  }

 private:
  std::string root_path_;
  int max_depth_;
  BigRat target_r_;
  BigRat target_c_;
  int num_workers_;
  std::string output_dir_;
  bool revalidate_ = false;
  int checkpoint_minutes_ = 15;

  std::unique_ptr<TreeNode> root_;
  CertificateCache cache_;
};

static void DiagnosePath(const std::string &path) {
  std::cout << "=== DIAGNOSING PATH: \"" << path << "\" ===\n";
  TriangleQ tri = TriangleFromPath(path);
  std::cout << "Corners:\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  c[" << i << "] = ("
              << tri.corners[i].x.ToString() << ", "
              << tri.corners[i].y.ToString() << ", "
              << tri.corners[i].z.ToString() << ")"
              << " (" << tri.corners[i].x.ToDouble() << ", "
              << tri.corners[i].y.ToDouble() << ", "
              << tri.corners[i].z.ToDouble() << ")\n";
  }
  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  std::cout << "Centroid: (" << centroid.x << ", " << centroid.y << ", " << centroid.z << ")\n";
  double diam = std::max({yocto::length(tri_f[0] - tri_f[1]), yocto::length(tri_f[1] - tri_f[2]), yocto::length(tri_f[2] - tri_f[0])});
  std::cout << "Diameter: " << diam << " rad\n";

  // Upper bounds
  std::vector<CandidateTriple> candidates;
  GenerateCandidatesForView(centroid, tri, false, 4, true, 2e-14, &candidates);
  std::cout << "Centroid candidate count (unconstrained): " << candidates.size() << "\n";
  std::vector<vec3> pts;
  for (const auto &c : candidates) pts.push_back(c.normalized_a);
  BigRat c_upper, r_upper;
  EstimateUpperBounds(tri, pts, &c_upper, &r_upper);
  std::cout << "Estimated c_upper: " << c_upper.ToString() << " (" << c_upper.ToDouble() << ")\n";
  std::cout << "Estimated r_upper: " << r_upper.ToString() << " (" << r_upper.ToDouble() << ")\n";

  // Check passes
  struct Pass {
    int cone_samples;
    bool include_boundaries;
    double screen_support_error;
  };
  std::vector<Pass> passes = {
    {4, false, 2e-14},
    {4, true, 2e-14},
    {5, true, 2e-14},
    {6, true, 2e-14}
  };

  for (size_t p = 0; p < passes.size(); p++) {
    const auto &pass = passes[p];
    std::cout << "\n--- Pass " << p << " (cone=" << pass.cone_samples
              << ", bdry=" << pass.include_boundaries << ") ---\n";
    std::vector<CandidateTriple> all_cands;
    std::vector<vec3> sample_views = {centroid, tri_f[0], tri_f[1], tri_f[2]};
    for (size_t s = 0; s < sample_views.size(); s++) {
      std::vector<CandidateTriple> v_cands;
      GenerateCandidatesForView(sample_views[s], tri, true, pass.cone_samples, pass.include_boundaries, pass.screen_support_error, &v_cands);
      std::cout << "  Sample view " << s << " generated " << v_cands.size() << " valid candidates over tri.\n";
      all_cands.insert(all_cands.end(), v_cands.begin(), v_cands.end());
    }

    std::vector<CandidateTriple> cand_dedup;
    std::vector<vec3> pts_dedup;
    for (const auto &c : all_cands) {
      bool dup = false;
      for (const auto &ex : pts_dedup) {
        if (yocto::length(ex - c.normalized_a) < 1e-6) { dup = true; break; }
      }
      if (!dup) {
        pts_dedup.push_back(c.normalized_a);
        cand_dedup.push_back(c);
      }
    }
    std::cout << "  Total unique candidates: " << cand_dedup.size() << "\n";
    vec3 min_p = pts_dedup[0], max_p = pts_dedup[0];
    for (const auto &p : pts_dedup) {
      min_p = {std::min(min_p.x, p.x), std::min(min_p.y, p.y), std::min(min_p.z, p.z)};
      max_p = {std::max(max_p.x, p.x), std::max(max_p.y, p.y), std::max(max_p.z, p.z)};
    }
    std::cout << "  Bounding box of pts_dedup: X ["
              << min_p.x << ", " << max_p.x << "] Y ["
              << min_p.y << ", " << max_p.y << "] Z ["
              << min_p.z << ", " << max_p.z << "]\n";
    double min_supp = 1e30;
    std::mt19937 r_test(42);
    std::normal_distribution<double> g_test(0.0, 1.0);
    for (int s = 0; s < 5000; s++) {
      vec3 u = {g_test(r_test), g_test(r_test), g_test(r_test)};
      double len = yocto::length(u);
      if (len < 1e-12) continue;
      u = u / len;
      double max_dot = -1e30;
      for (const auto &p : pts_dedup) max_dot = std::max(max_dot, yocto::dot(u, p));
      min_supp = std::min(min_supp, max_dot);
    }
    std::cout << "  pts_dedup min_supp: " << min_supp << "\n";
    BigRat dedup_c_upper, dedup_r_upper;
    EstimateUpperBounds(tri, pts_dedup, &dedup_c_upper, &dedup_r_upper);
    std::cout << "  Convex hull of valid tri candidates: c_upper = "
              << dedup_c_upper.ToString() << " (" << dedup_c_upper.ToDouble() << ")\n";
    if (cand_dedup.size() < 4) {
      std::cout << "  Insufficient candidates (< 4) for tet enclosure.\n";
      continue;
    }

    // 1. Try Extremal
    std::array<int, 4> ext_idx;
    if (FindExtremalTetrahedron(pts_dedup, &ext_idx)) {
      std::cout << "  FindExtremalTetrahedron found tet: indices ["
                << ext_idx[0] << ", " << ext_idx[1] << ", " << ext_idx[2] << ", " << ext_idx[3] << "]\n";
      TubeCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = cand_dedup[ext_idx[a]].contacts[0];
        test_cert.axes[a].contacts[1] = cand_dedup[ext_idx[a]].contacts[1];
        test_cert.axes[a].contacts[2] = cand_dedup[ext_idx[a]].contacts[2];
      }
      TubeCertificate out_cert;
      std::string fail_reason;
      if (AuditCertificateAdaptive(tri, test_cert, &out_cert, &fail_reason)) {
        std::cout << AGREEN("  Extremal tet SUCCESS! c = ") << out_cert.c.ToString() << ", r = " << out_cert.r.ToString() << "\n";
        return;
      } else {
        std::cout << "  Extremal tet audit failed: " << fail_reason << "\n";
      }
    } else {
      std::cout << "  FindExtremalTetrahedron failed to find enclosing tet.\n";
    }

    // 2. Try Balanced
    std::array<int, 4> wolfe_idx;
    if (Tube229::FindBalancedTetrahedron(pts_dedup, &wolfe_idx)) {
      std::cout << "  FindBalancedTetrahedron found tet: indices ["
                << wolfe_idx[0] << ", " << wolfe_idx[1] << ", " << wolfe_idx[2] << ", " << wolfe_idx[3] << "]\n";
      TubeCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = cand_dedup[wolfe_idx[a]].contacts[0];
        test_cert.axes[a].contacts[1] = cand_dedup[wolfe_idx[a]].contacts[1];
        test_cert.axes[a].contacts[2] = cand_dedup[wolfe_idx[a]].contacts[2];
      }
      TubeCertificate out_cert;
      std::string fail_reason;
      if (AuditCertificateAdaptive(tri, test_cert, &out_cert, &fail_reason)) {
        std::cout << AGREEN("  Balanced tet SUCCESS! c = ") << out_cert.c.ToString() << ", r = " << out_cert.r.ToString() << "\n";
        return;
      } else {
        std::cout << "  Balanced tet audit failed: " << fail_reason << "\n";
      }
    } else {
      std::cout << "  FindBalancedTetrahedron failed to find enclosing tet.\n";
    }

    // 3. Pool search
    std::set<int> pool_set;
    for (int d = 0; d < 1000; d++) {
      double y = 1.0 - (d / 999.0) * 2.0;
      double radius = std::sqrt(std::max(0.0, 1.0 - y * y));
      double theta = 2.39996322972865332 * d;
      vec3 dir = {std::cos(theta) * radius, y, std::sin(theta) * radius};
      int best_hi = 0, best_lo = 0;
      double max_v = yocto::dot(pts_dedup[0], dir);
      double min_v = max_v;
      for (size_t i = 1; i < pts_dedup.size(); i++) {
        double v = yocto::dot(pts_dedup[i], dir);
        if (v > max_v) { max_v = v; best_hi = i; }
        if (v < min_v) { min_v = v; best_lo = i; }
      }
      pool_set.insert(best_hi);
      pool_set.insert(best_lo);
    }
    std::vector<int> pool(pool_set.begin(), pool_set.end());
    std::cout << "  Pool size: " << pool.size() << " extreme points\n";

    struct ScoredTet {
      double margin;
      std::array<int, 4> indices;
    };
    std::vector<ScoredTet> scored;
    int P = pool.size();
    if (P >= 4) {
      uint64_t comb4 = (uint64_t)P * (P - 1) * (P - 2) * (P - 3) / 24;
      std::cout << "  Comb4: " << comb4 << "\n";
      if (comb4 <= 100000) {
        for (int i = 0; i < P; i++) {
          for (int j = i + 1; j < P; j++) {
            for (int k = j + 1; k < P; k++) {
              for (int l = k + 1; l < P; l++) {
                vec3 tpts[4] = {pts_dedup[pool[i]], pts_dedup[pool[j]], pts_dedup[pool[k]], pts_dedup[pool[l]]};
                double margin;
                double bary[4];
                if (TetrahedronOriginMargin(tpts, &margin, bary)) {
                  scored.push_back({margin, {pool[i], pool[j], pool[k], pool[l]}});
                }
              }
            }
          }
        }
      } else {
        std::mt19937 rng(1337 + path.size() * 31);
        std::uniform_int_distribution<int> dist(0, P - 1);
        for (int trial = 0; trial < 100000; trial++) {
          int i0 = dist(rng), i1 = dist(rng), i2 = dist(rng), i3 = dist(rng);
          if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
          vec3 tpts[4] = {pts_dedup[pool[i0]], pts_dedup[pool[i1]], pts_dedup[pool[i2]], pts_dedup[pool[i3]]};
          double margin;
          double bary[4];
          if (TetrahedronOriginMargin(tpts, &margin, bary)) {
            scored.push_back({margin, {pool[i0], pool[i1], pool[i2], pool[i3]}});
          }
        }
      }
    }
    if (scored.empty()) {
      std::cout << "  Initial pool did not enclose origin; running cutting plane refinement...\n";
      for (int iter = 0; iter < 50; iter++) {
        std::vector<int> cur_pool(pool_set.begin(), pool_set.end());
        ClosestResult closest = ClosestOriginFace(pts_dedup, cur_pool);
        std::cout << "    iter " << iter << " closest.key: " << closest.key << " support size: " << closest.support.size() << "\n";
        vec3 v = closest.point;
        if (closest.key < 1e-10) {
          std::cout << "    closest.key < 1e-10 (origin inside conv(cur_pool))!\n";
          if (closest.support.size() == 3) {
            int i0 = closest.support[0], i1 = closest.support[1], i2 = closest.support[2];
            vec3 face_norm = yocto::cross(pts_dedup[i1] - pts_dedup[i0], pts_dedup[i2] - pts_dedup[i0]);
            double len = yocto::length(face_norm);
            if (len > 1e-9) {
              face_norm = face_norm / len;
              int best_pos = -1, best_neg = -1;
              double max_pos = -1e30, max_neg = -1e30;
              for (size_t i = 0; i < pts_dedup.size(); i++) {
                double dp = yocto::dot(pts_dedup[i], face_norm);
                if (dp > max_pos) { max_pos = dp; best_pos = i; }
                double dn = yocto::dot(pts_dedup[i], -face_norm);
                if (dn > max_neg) { max_neg = dn; best_neg = i; }
              }
              std::cout << "    Normal piercing: best_pos=" << best_pos << " (" << max_pos << ") best_neg=" << best_neg << " (" << max_neg << ")\n";
              if (best_pos >= 0 && best_neg >= 0 && max_pos > 1e-9 && max_neg > 1e-9 && best_pos != best_neg) {
                int tri_edges[3][2] = {{i0, i1}, {i1, i2}, {i2, i0}};
                for (int e = 0; e < 3; e++) {
                  int e0 = tri_edges[e][0], e1 = tri_edges[e][1];
                  if (best_pos == e0 || best_pos == e1 || best_neg == e0 || best_neg == e1) continue;
                  vec3 tpts[4] = {pts_dedup[e0], pts_dedup[e1], pts_dedup[best_pos], pts_dedup[best_neg]};
                  double margin; double bary[4];
                  if (TetrahedronOriginMargin(tpts, &margin, bary)) {
                    scored.push_back({margin, {e0, e1, best_pos, best_neg}});
                  }
                }
                if (best_neg >= 0 && best_neg != i0 && best_neg != i1 && best_neg != i2) {
                  vec3 tpts[4] = {pts_dedup[i0], pts_dedup[i1], pts_dedup[i2], pts_dedup[best_neg]};
                  double margin; double bary[4];
                  if (TetrahedronOriginMargin(tpts, &margin, bary)) {
                    scored.push_back({margin, {i0, i1, i2, best_neg}});
                  }
                }
              }
              std::cout << "    Normal piercing found " << scored.size() << " enclosing tets!\n";
              if (!scored.empty()) break;
              double sum_d = 0;
              for (int p_idx : cur_pool) sum_d += yocto::dot(pts_dedup[p_idx], face_norm);
              if (sum_d < 0) face_norm = -face_norm;
              v = face_norm;
            }
          } else {
            double vlen = yocto::length(v);
            if (vlen > 1e-15) v = v / vlen;
          }
        } else {
          double vlen = yocto::length(v);
          if (vlen > 1e-15) v = v / vlen;
        }

        int best_i = -1;
        double max_dot = -1e30;
        for (size_t i = 0; i < pts_dedup.size(); i++) {
          double d = yocto::dot(pts_dedup[i], -v);
          if (d > max_dot) { max_dot = d; best_i = i; }
        }
        std::cout << "    max_dot in direction -v: " << max_dot << " best_i: " << best_i << " already in pool: " << pool_set.count(best_i) << "\n";
        if (max_dot <= 1e-12 || pool_set.count(best_i)) break;
        pool_set.insert(best_i);
        for (int i : cur_pool) {
          for (int j : cur_pool) {
            if (j <= i) continue;
            for (int k : cur_pool) {
              if (k <= j) continue;
              vec3 tpts[4] = {pts_dedup[i], pts_dedup[j], pts_dedup[k], pts_dedup[best_i]};
              double margin;
              double bary[4];
              if (TetrahedronOriginMargin(tpts, &margin, bary)) {
                scored.push_back({margin, {i, j, k, best_i}});
              }
            }
          }
        }
        if (!scored.empty()) {
          std::cout << "    Cutting plane found " << scored.size() << " enclosing tets!\n";
          break;
        }
      }
    }
    std::cout << "  Scored enclosing tets: " << scored.size() << "\n";
    if (!scored.empty()) {
      std::sort(scored.begin(), scored.end(), [](const ScoredTet &a, const ScoredTet &b) {
        return a.margin > b.margin;
      });
      std::cout << "  Best tet margin: " << scored[0].margin << "\n";
      for (size_t idx = 0; idx < std::min((size_t)10, scored.size()); idx++) {
        TubeCertificate test_cert;
        for (int a = 0; a < 4; a++) {
          int c_idx = scored[idx].indices[a];
          test_cert.axes[a].contacts[0] = cand_dedup[c_idx].contacts[0];
          test_cert.axes[a].contacts[1] = cand_dedup[c_idx].contacts[1];
          test_cert.axes[a].contacts[2] = cand_dedup[c_idx].contacts[2];
        }
        TubeCertificate out_cert;
        std::string fail_reason;
        std::cout << "Trying scored tet " << idx << "...\n";
        for (int a = 0; a < 4; a++) {
          ContactInfo c[3] = {test_cert.axes[a].contacts[0], test_cert.axes[a].contacts[1], test_cert.axes[a].contacts[2]};
          BigVecQ3 center; BigRat delta; std::string rsn;
          bool ok = AuditAxis(tri, c, &out_cert.axes[a], &center, &delta, &rsn);
          std::cout << "  pre-check axis " << a << ": " << (ok ? "OK" : "FAIL") << " (" << rsn << ")"
                    << " [0]=(" << c[0].vertex << "," << c[0].edge_start << "->" << c[0].edge_finish << "," << c[0].edge_start2 << "->" << c[0].edge_finish2 << "," << c[0].mix << ")"
                    << " [1]=(" << c[1].vertex << "," << c[1].edge_start << "->" << c[1].edge_finish << "," << c[1].edge_start2 << "->" << c[1].edge_finish2 << "," << c[1].mix << ")"
                    << " [2]=(" << c[2].vertex << "," << c[2].edge_start << "->" << c[2].edge_finish << "," << c[2].edge_start2 << "->" << c[2].edge_finish2 << "," << c[2].mix << ")\n";
        }
        if (AuditCertificateAdaptive(tri, test_cert, &out_cert, &fail_reason)) {
          std::cout << AGREEN("  Scored tet SUCCESS! c = ") << out_cert.c.ToString() << ", r = " << out_cert.r.ToString() << ", delta = " << out_cert.delta.ToString() << "\n";
          for (int a = 0; a < 4; a++) {
            const auto &ax = out_cert.axes[a];
            std::cout << "  Axis " << a << " B=" << ax.B.ToString() << "\n";
            for (int m = 0; m < 3; m++) {
              std::cout << "    contact " << m << ": inner=" << ax.contacts[m].vertex
                        << " (" << ax.contacts[m].edge_start << "->" << ax.contacts[m].edge_finish << ") & ("
                        << ax.contacts[m].edge_start2 << "->" << ax.contacts[m].edge_finish2 << ") mix="
                        << ax.contacts[m].mix << " witness=" << ax.nonzero_witness[m] << "\n";
            }
          }
          return;
        } else if (idx == 0) {
          std::cout << "  Best scored tet audit fail: " << fail_reason << "\n";
        }
      }
    }
  }

  std::cout << "\nAttempting Tube229 smart synthesis...\n";
  TubeCertificate tube_cert;
  if (Tube229::SynthesizeCertificate(tri, path.size(), &tube_cert)) {
    std::cout << AGREEN("Tube229 synthesis SUCCESS!") << " c = " << tube_cert.c.ToString() << ", r = " << tube_cert.r.ToString() << "\n";
    return;
  }

  std::cout << "\nDiagnosis complete. Node failed to certify with current settings.\n";
}

// ============================================================================
// MAIN CLI
// ============================================================================

int main(int argc, char **argv) {
  std::string root_path = "0";
  int max_depth = -1;
  int min_depth = -1;
  bool ancestor_sweep = false;
  bool leaf_sweep = false;
  std::string target_r_str = "1/6000000";
  std::string target_c_str = "1018/10000000";
  int threads = 8;
  int checkpoint_minutes = 15;
  std::string output_dir = ".artifacts/nopert229";
  bool revalidate = false;

  std::signal(SIGINT, SignalHandler);
  std::signal(SIGTERM, SignalHandler);

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--diagnose" && i + 1 < argc) {
      std::string path = argv[++i];
      DiagnosePath(path);
      return 0;
    } else if (arg == "--root_path" && i + 1 < argc) root_path = argv[++i];
    else if (arg == "--max_depth" && i + 1 < argc) max_depth = std::stoi(argv[++i]);
    else if (arg == "--min_depth" && i + 1 < argc) min_depth = std::stoi(argv[++i]);
    else if (arg == "--ancestor_sweep") ancestor_sweep = true;
    else if (arg == "--leaf_sweep") leaf_sweep = true;
    else if (arg == "--target_r" && i + 1 < argc) target_r_str = argv[++i];
    else if (arg == "--target_c" && i + 1 < argc) target_c_str = argv[++i];
    else if (arg == "--threads" && i + 1 < argc) threads = std::stoi(argv[++i]);
    else if (arg == "--checkpoint_minutes" && i + 1 < argc) checkpoint_minutes = std::stoi(argv[++i]);
    else if (arg == "--output_dir" && i + 1 < argc) output_dir = argv[++i];
    else if (arg == "--revalidate") revalidate = true;
  }

  BigRat target_r(target_r_str);
  BigRat target_c(target_c_str);

  if (leaf_sweep) {
    if (min_depth < 0) min_depth = 19;
    if (max_depth < 0) max_depth = 30;
    IncrementalTubeManager manager(root_path, max_depth, target_r, target_c, threads, output_dir, revalidate);
    manager.set_checkpoint_minutes(checkpoint_minutes);
    manager.RunLeafSweep(min_depth, max_depth);
  } else if (ancestor_sweep) {
    if (min_depth < 0) min_depth = 1;
    if (max_depth < 0) max_depth = 15;
    IncrementalTubeManager manager(root_path, max_depth, target_r, target_c, threads, output_dir, revalidate);
    manager.set_checkpoint_minutes(checkpoint_minutes);
    manager.RunAncestorSweep(min_depth, max_depth);
  } else {
    if (max_depth < 0) max_depth = 10;
    IncrementalTubeManager manager(root_path, max_depth, target_r, target_c, threads, output_dir, revalidate);
    manager.set_checkpoint_minutes(checkpoint_minutes);
    manager.Run();
  }
  return 0;
}

