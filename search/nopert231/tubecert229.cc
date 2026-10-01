// Identity Tube Local Certificate Search for Nopert #229
// High-performance multithreaded C++ implementation with exact GMP BigRat audit.

#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <ctime>
#include <filesystem>
#include <format>
#include <fstream>
#include <iostream>
#include <mutex>
#include <numbers>
#include <numeric>
#include <random>
#include <set>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "ansi.h"
#include "base/logging.h"
#include "base/stringprintf.h"
#include "bignum/big-overloads.h"
#include "bignum/big.h"
#include "nopert229.h"
#include "util.h"
#include "yocto-math.h"
#include "rapidjson/document.h"
#include "rapidjson/error/en.h"
#include "tubetree229.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

// Polyhedron #229 rational vertices are accessed via GetVerticesQ() from nopert229.h

static inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

using tubetree229::TriangleQ;
using tubetree229::ContactInfo;
using tubetree229::kMixScale;
using tubetree229::AxisCertificate;
using LocalCertificate = tubetree229::TubeCertificate;

// Quadratic polynomial in 3 variables with basis:
// 1, x, y, z, x², xy, xz, y², yz, z²
struct QPoly {
  BigRat c[10];
  QPoly() {
    for (int i = 0; i < 10; i++) c[i] = BigRat(0);
  }
  static QPoly MulLinear(const BigVecQ3 &a, const BigVecQ3 &b) {
    QPoly p;
    // homogeneous degree 2
    p.c[4] = a.x * b.x;
    p.c[5] = a.x * b.y + a.y * b.x;
    p.c[6] = a.x * b.z + a.z * b.x;
    p.c[7] = a.y * b.y;
    p.c[8] = a.y * b.z + a.z * b.y;
    p.c[9] = a.z * b.z;
    return p;
  }
  void AddScaled(const BigRat &s, const QPoly &o) {
    for (int i = 0; i < 10; i++) {
      c[i] = c[i] + s * o.c[i];
    }
  }
  std::pair<BigRat, BigRat> EvalCentered(const BigVecQ3 &center, const BigVecQ3 &radius) const {
    BigRat x = center.x, y = center.y, z = center.z;
    BigRat rx = radius.x, ry = radius.y, rz = radius.z;
    BigRat value = c[0] + c[1]*x + c[2]*y + c[3]*z + c[4]*x*x +
                   c[5]*x*y + c[6]*x*z + c[7]*y*y + c[8]*y*z + c[9]*z*z;
    BigRat gx = c[1] + BigRat(2)*c[4]*x + c[5]*y + c[6]*z;
    BigRat gy = c[2] + c[5]*x + BigRat(2)*c[7]*y + c[8]*z;
    BigRat gz = c[3] + c[6]*x + c[8]*y + BigRat(2)*c[9]*z;
    BigRat lin_rad = (gx < 0 ? -gx : gx) * rx +
                     (gy < 0 ? -gy : gy) * ry +
                     (gz < 0 ? -gz : gz) * rz;
    BigRat quad_rad = (c[4] < 0 ? -c[4] : c[4]) * rx * rx +
                      (c[5] < 0 ? -c[5] : c[5]) * rx * ry +
                      (c[6] < 0 ? -c[6] : c[6]) * rx * rz +
                      (c[7] < 0 ? -c[7] : c[7]) * ry * ry +
                      (c[8] < 0 ? -c[8] : c[8]) * ry * rz +
                      (c[9] < 0 ? -c[9] : c[9]) * rz * rz;
    return {value, lin_rad + quad_rad};
  }
};

static BigVecQ3 GetExactEdge(const ContactInfo &c) {
  const BigVecQ3 &v_start = VertexQ(c.edge_start);
  const BigVecQ3 &v_finish = VertexQ(c.edge_finish);
  const BigVecQ3 &v_start2 = VertexQ(c.edge_start2);
  const BigVecQ3 &v_finish2 = VertexQ(c.edge_finish2);
  BigRat mixQ(c.mix, kMixScale);
  return (v_start - v_finish) * mixQ + (v_start2 - v_finish2) * (BigRat(1) - mixQ);
}

static inline BigRat CeilTo(const BigRat &x, int64_t denom) {
  BigRat scaled = x * BigRat(denom);
  BigInt num = scaled.Numerator();
  BigInt den = scaled.Denominator();
  BigInt q;
  if (num >= BigInt(0)) {
    q = (num + den - BigInt(1)) / den;
  } else {
    q = num / den;
  }
  return BigRat(q, BigInt(denom));
}

static inline BigRat FloorTo(const BigRat &x, int64_t denom) {
  BigRat scaled = x * BigRat(denom);
  BigInt num = scaled.Numerator();
  BigInt den = scaled.Denominator();
  BigInt q;
  if (num >= BigInt(0)) {
    q = num / den;
  } else {
    q = (num - den + BigInt(1)) / den;
  }
  return BigRat(q, BigInt(denom));
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
                 (contacts[m].mix == kMixScale && sel == contacts[m].edge_finish && k == contacts[m].edge_start) ||
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

  // Variation polynomials for each coordinate
  QPoly polys[3];
  for (int coord = 0; coord < 3; coord++) {
    for (int i = 0; i < 3; i++) {
      const BigVecQ3 &v_supp = VertexQ(contacts[i].vertex);
      // lift coeff
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

  BigRat variation_error(150, 10000000000LL); // 150 * KAPPA (KAPPA = 10^-10 in Lean 4)
  BigRat exact_delta = (evals[0].second + evals[1].second + evals[2].second + BigRat(3) * variation_error) / B;
  *out_delta = CeilTo(exact_delta, 1000000000LL);
  return true;
}

// Re-audit an entire 4-axis certificate on triangle tri
// If out_cover/out_delta are given, they receive the cage's cover radius and
// variation delta whenever all four axes audit (even if the cage fails).
static bool ReauditCertificate(const TriangleQ &tri, const LocalCertificate &in_cert,
                               const BigRat &target_c, const BigRat &tube_radius,
                               LocalCertificate *out_cert,
                               std::string *fail_reason = nullptr,
                               BigRat *out_cover = nullptr,
                               BigRat *out_delta = nullptr) {
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
  if (out_cover) *out_cover = cover_radius;
  if (out_delta) *out_delta = delta;

  if (target_c > BigRat(0) && cover_radius <= target_c) {
    if (fail_reason) *fail_reason = StringPrintf("cover_radius <= target_c (cover=%s, target=%s)",
                                                 cover_radius.ToString().c_str(), target_c.ToString().c_str());
    return false;
  }

  BigRat margin = cover_radius - delta;
  if (margin <= BigRat(0)) {
    if (fail_reason) *fail_reason = StringPrintf("cover <= delta (cover=%s, delta=%s)",
                                                 cover_radius.ToString().c_str(), delta.ToString().c_str());
    return false;
  }

  BigRat c;
  if (margin >= BigRat("1/1000000000")) {
    c = FloorTo(margin, 1000000000LL);
  } else {
    c = margin * BigRat(19, 20);
  }

  if (target_c > BigRat(0) && c < target_c) {
    if (fail_reason) *fail_reason = StringPrintf("c < target_c (c=%s, target=%s, cover=%s, delta=%s)",
                                                 c.ToString().c_str(), target_c.ToString().c_str(),
                                                 cover_radius.ToString().c_str(), delta.ToString().c_str());
    return false;
  }

  // Check containment of the 6 test points: +- 7/4 (c + delta) e_k
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

  // Check allowable tube radius condition: r^2 (1 + c^2) <= 4 c^2
  // We want to find largest allowable r from a set of standard fractions:
  const BigRat candidate_rs[] = {
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
  BigRat certified_r(0);
  for (const auto &cand : candidate_rs) {
    if (cand * cand * (BigRat(1) + c * c) <= BigRat(4) * c * c) {
      certified_r = cand;
      break;
    }
  }
  if (tube_radius > BigRat(0) && certified_r < tube_radius) {
    if (tube_radius * tube_radius * (BigRat(1) + c * c) <= BigRat(4) * c * c) {
      certified_r = tube_radius;
    } else {
      if (fail_reason) *fail_reason = StringPrintf("certified_r < tube_radius (r=%s, target=%s, c=%s)",
                                                   certified_r.ToString().c_str(), tube_radius.ToString().c_str(), c.ToString().c_str());
      return false;
    }
  }

  out_cert->c = c;
  out_cert->delta = delta;
  out_cert->r = certified_r;
  return true;
}

// ---------------- Candidate Synthesis Engine ----------------

static inline double Cross2(const vec2 &a, const vec2 &b) {
  return a.x * b.y - a.y * b.x;
}

static std::vector<int> ConvexHull2D(const std::vector<vec2> &points) {
  int n = points.size();
  std::vector<int> p(n);
  std::iota(p.begin(), p.end(), 0);
  std::sort(p.begin(), p.end(), [&](int a, int b) {
    if (points[a].x != points[b].x) return points[a].x < points[b].x;
    return points[a].y < points[b].y;
  });

  auto half = [&](const std::vector<int> &indices) {
    std::vector<int> ans;
    for (int idx : indices) {
      while (ans.size() >= 2) {
        vec2 a = points[ans[ans.size() - 2]];
        vec2 b = points[ans[ans.size() - 1]];
        vec2 pt = points[idx];
        vec2 ab = b - a;
        vec2 bp = pt - b;
        if (Cross2(ab, bp) > 1e-14) break;
        ans.pop_back();
      }
      ans.push_back(idx);
    }
    return ans;
  };

  std::vector<int> lower = half(p);
  std::vector<int> rev_p = p;
  std::reverse(rev_p.begin(), rev_p.end());
  std::vector<int> upper = half(rev_p);

  std::vector<int> hull;
  if (!lower.empty()) lower.pop_back();
  if (!upper.empty()) upper.pop_back();
  hull.insert(hull.end(), lower.begin(), lower.end());
  hull.insert(hull.end(), upper.begin(), upper.end());
  return hull;
}

struct CandidateTriple {
  ContactInfo contacts[3];
  vec3 normalized_a;
  double strict_slack = 0.0;
};

static inline vec3 GetDoubleEdge(const ContactInfo &c) {
  vec3 v_start = Vertex(c.edge_start);
  vec3 v_finish = Vertex(c.edge_finish);
  vec3 v_start2 = Vertex(c.edge_start2);
  vec3 v_finish2 = Vertex(c.edge_finish2);
  double mixD = c.mix / (double)kMixScale;
  return (v_start - v_finish) * mixD + (v_start2 - v_finish2) * (1.0 - mixD);
}

static void GenerateCandidatesForView(
    const vec3 &view,
    const TriangleQ &tri,
    int cone_samples,
    bool include_boundaries,
    double screen_support_error,
    std::vector<CandidateTriple> *out_candidates) {
  double vlen = yocto::length(view);
  if (vlen < 1e-12) return;
  vec3 unit_view = view / vlen;

  int axis_index = 0;
  double min_abs = 1e30;
  for (int i = 0; i < 3; i++) {
    if (std::abs(unit_view[i]) < min_abs) {
      min_abs = std::abs(unit_view[i]);
      axis_index = i;
    }
  }
  vec3 axis = (axis_index == 0 ? vec3{1, 0, 0} : (axis_index == 1 ? vec3{0, 1, 0} : vec3{0, 0, 1}));
  vec3 first = yocto::cross(unit_view, axis);
  double first_len = yocto::length(first);
  if (first_len < 1e-12) return;
  first = first / first_len;
  vec3 second = yocto::cross(unit_view, first);

  std::vector<vec2> projected(20);
  for (int k = 0; k < 20; k++) {
    projected[k] = vec2{
      yocto::dot(Vertex(k), first),
      yocto::dot(Vertex(k), second),
    };
  }
  std::vector<int> cycle = ConvexHull2D(projected);
  int H = cycle.size();
  if (H < 3) return;

  std::vector<ContactInfo> contacts;
  std::vector<vec3> lifts;
  for (int pos = 0; pos < H; pos++) {
    int vertex = cycle[pos];
    int previous = cycle[(pos - 1 + H) % H];
    int following = cycle[(pos + 1) % H];

    std::vector<double> samples;
    for (int s = 0; s < cone_samples; s++) {
      samples.push_back((s + 1.0) / (cone_samples + 1.0));
    }
    if (include_boundaries) {
      samples.push_back(0.0);
      samples.push_back(0.001);
      samples.push_back(0.999);
      samples.push_back(1.0);
      std::sort(samples.begin(), samples.end());
      samples.erase(std::unique(samples.begin(), samples.end()), samples.end());
    }

    for (double lam : samples) {
      int mix = std::clamp(static_cast<int>(std::round(kMixScale * lam)), 0, kMixScale);
      ContactInfo ci;
      ci.vertex = vertex;
      ci.edge_start = previous;
      ci.edge_finish = vertex;
      ci.edge_start2 = vertex;
      ci.edge_finish2 = following;
      ci.mix = mix;
      vec3 edge = GetDoubleEdge(ci);
      vec3 lift = yocto::cross(unit_view, edge);
      contacts.push_back(ci);
      lifts.push_back(lift);
    }
  }

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };

  struct ContactSupportData {
    vec3 edge;
    int selected;
    double strict_slack;
    bool support_ok;
  };

  std::vector<ContactSupportData> supp_cache(contacts.size());
  for (size_t i = 0; i < contacts.size(); i++) {
    const auto &c = contacts[i];
    vec3 edge = GetDoubleEdge(c);
    int sel = c.vertex;
    double strict_slack = 1e30;
    bool ok = true;
    for (int k = 0; k < 20; k++) {
      bool tie = (k == sel) ||
                 (c.mix == kMixScale && sel == c.edge_finish && k == c.edge_start) ||
                 (c.mix == 0 && sel == c.edge_start2 && k == c.edge_finish2);
      if (tie) continue;
      vec3 delta = Vertex(k) - Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta);
      double upper = std::max({yocto::dot(tri_f[0], coeff),
                               yocto::dot(tri_f[1], coeff),
                               yocto::dot(tri_f[2], coeff)}) + screen_support_error;
      strict_slack = std::min(strict_slack, -upper);
      if (upper > 0) {
        ok = false;
        break;
      }
    }
    supp_cache[i] = {edge, sel, strict_slack, ok};
  }

  // Pre-filter to contacts whose support inequality passes
  std::vector<int> valid_idx;
  for (size_t i = 0; i < contacts.size(); i++) {
    if (supp_cache[i].support_ok) valid_idx.push_back(i);
  }

  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  int V = valid_idx.size();

  for (int ii = 0; ii < V; ii++) {
    int i = valid_idx[ii];
    for (int jj = ii + 1; jj < V; jj++) {
      int j = valid_idx[jj];
      for (int kk = jj + 1; kk < V; kk++) {
        int k = valid_idx[kk];

        vec3 lifts_triple[3] = {lifts[i], lifts[j], lifts[k]};
        vec3 w = {yocto::dot(unit_view, yocto::cross(lifts_triple[1], lifts_triple[2])),
                  yocto::dot(unit_view, yocto::cross(lifts_triple[2], lifts_triple[0])),
                  yocto::dot(unit_view, yocto::cross(lifts_triple[0], lifts_triple[1]))};
        if (w[0] <= 1e-12 && w[1] <= 1e-12 && w[2] <= 1e-12) {
          w = -w;
        }
        if (w[0] < -1e-10 || w[1] < -1e-10 || w[2] < -1e-10) continue;

        ContactInfo sel_contacts[3] = {contacts[i], contacts[j], contacts[k]};
        vec3 c_edges[3] = {supp_cache[i].edge, supp_cache[j].edge, supp_cache[k].edge};
        ContactSupportData c_supp[3] = {supp_cache[i], supp_cache[j], supp_cache[k]};

        vec3 probe = {yocto::dot(tri_f[0], yocto::cross(c_edges[1], c_edges[2])),
                      yocto::dot(tri_f[0], yocto::cross(c_edges[2], c_edges[0])),
                      yocto::dot(tri_f[0], yocto::cross(c_edges[0], c_edges[1]))};
        if (std::max({probe[0], probe[1], probe[2]}) < 0) {
          std::swap(sel_contacts[1], sel_contacts[2]);
          std::swap(c_edges[1], c_edges[2]);
          std::swap(c_supp[1], c_supp[2]);
        }

        vec3 weight_coeffs[3] = {
          yocto::cross(c_edges[1], c_edges[2]),
          yocto::cross(c_edges[2], c_edges[0]),
          yocto::cross(c_edges[0], c_edges[1])
        };

        bool weight_ok = true;
        double max_weight_lower = -1e30;
        double weights_at_max[3] = {0, 0, 0};
        for (int m = 0; m < 3; m++) {
          double w0 = yocto::dot(tri_f[0], weight_coeffs[m]);
          double w1 = yocto::dot(tri_f[1], weight_coeffs[m]);
          double w2 = yocto::dot(tri_f[2], weight_coeffs[m]);
          double w_min = std::min({w0, w1, w2}) - screen_support_error;
          double w_max = std::max({w0, w1, w2}) + screen_support_error;
          if (w_min < 0) { weight_ok = false; break; }
          max_weight_lower = std::max(max_weight_lower, w_min);
          weights_at_max[m] = w_max;
        }
        if (!weight_ok || max_weight_lower <= 0) continue;

        double strict_slack = std::min({c_supp[0].strict_slack, c_supp[1].strict_slack, c_supp[2].strict_slack});

        vec3 weights = {yocto::dot(centroid, weight_coeffs[0]),
                        yocto::dot(centroid, weight_coeffs[1]),
                        yocto::dot(centroid, weight_coeffs[2])};
        double B = 2.0 * (weights_at_max[0] + weights_at_max[1] + weights_at_max[2]);
        vec3 variation = {0, 0, 0};
        for (int m = 0; m < 3; m++) {
          vec3 lift = yocto::cross(centroid, c_edges[m]);
          vec3 term = yocto::cross(Vertex(c_supp[m].selected), lift);
          variation = variation + term * weights[m];
        }
        vec3 normalized_a = variation / B;

        CandidateTriple cand;
        cand.contacts[0] = sel_contacts[0];
        cand.contacts[1] = sel_contacts[1];
        cand.contacts[2] = sel_contacts[2];
        cand.normalized_a = normalized_a;
        cand.strict_slack = strict_slack;
        out_candidates->push_back(cand);
      }
    }
  }
}

static bool SolveLinear4(const double A[4][4], const double b[4], double x[4]) {
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
    for (int c = 0; c < 5; c++) std::swap(aug[col][c], aug[pivot][c]);
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
  if (!SolveLinear4(A, b, bary)) return false;
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

static bool FindBalancedTetrahedron(const std::vector<vec3> &pts, std::array<int, 4> *out_indices, bool verbose = false) {
  int n = pts.size();
  if (n < 4) return false;
  int min_norm_idx = 0;
  double min_norm = yocto::dot(pts[0], pts[0]);
  for (int i = 1; i < n; i++) {
    double d = yocto::dot(pts[i], pts[i]);
    if (d < min_norm) { min_norm = d; min_norm_idx = i; }
  }
  std::vector<int> active = {min_norm_idx};
  std::set<std::pair<std::vector<int>, int>> seen;

  for (int iter = 0; iter < 100; iter++) {
    if (active.size() >= 4) {
      int m = active.size();
      for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
          for (int k = j + 1; k < m; k++) {
            for (int l = k + 1; l < m; l++) {
              vec3 tpts[4] = {pts[active[i]], pts[active[j]], pts[active[k]], pts[active[l]]};
              double margin;
              double bary[4];
              if (TetrahedronOriginMargin(tpts, &margin, bary)) {
                if (verbose) std::cout << "    [Wolfe] found enclosing tet on iter " << iter << " margin=" << margin << "\n";
                *out_indices = {active[i], active[j], active[k], active[l]};
                return true;
              }
            }
          }
        }
      }
    }

    ClosestResult closest = ClosestOriginFace(pts, active);
    if (closest.support.empty()) {
      if (verbose) std::cout << "    [Wolfe] abort: support empty on iter " << iter << "\n";
      return false;
    }
    active = closest.support;
    vec3 current = closest.point;
    double norm_sq = closest.key;

    int next_index = -1;
    double min_dot = 1e30;
    for (int i = 0; i < n; i++) {
      double d = yocto::dot(current, pts[i]);
      if (d < min_dot) { min_dot = d; next_index = i; }
    }
    double improvement = norm_sq - min_dot;
    if (improvement <= 1e-13 * std::max(1.0, norm_sq)) {
      if (verbose) std::cout << "    [Wolfe] abort: no improvement on iter " << iter << " (norm_sq=" << norm_sq << ", min_dot=" << min_dot << ")\n";
      return false;
    }

    if (std::find(active.begin(), active.end(), next_index) != active.end()) {
      if (verbose) std::cout << "    [Wolfe] abort: next_index already in active on iter " << iter << "\n";
      return false;
    }
    std::vector<int> sorted_active = active;
    std::sort(sorted_active.begin(), sorted_active.end());
    if (seen.count({sorted_active, next_index})) {
      if (verbose) std::cout << "    [Wolfe] abort: seen state on iter " << iter << "\n";
      return false;
    }
    seen.insert({sorted_active, next_index});
    active.push_back(next_index);
  }
  if (verbose) std::cout << "    [Wolfe] abort: max iters reached\n";
  return false;
}

// Returns upper bound on margin c achievable by any tetrahedron chosen from candidates,
// plus the maximum possible variation across triangle tri.
// If this upper bound is less than target_c, no descendant triangle can ever reach target_c.
static bool FindExtremalTetrahedron(const std::vector<vec3> &pts, double min_margin, std::array<int, 4> *out_indices, bool verbose = false) {
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

  double best_margin = -1e30;
  std::array<int, 4> best_idx = {-1, -1, -1, -1};

  for (int trial = 0; trial < 1000; trial++) {
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
      if (margin > best_margin) {
        best_margin = margin;
        best_idx = {idx[0], idx[1], idx[2], idx[3]};
        if (best_margin >= min_margin) {
          if (verbose) std::cout << "    [Extremal] found tet on trial " << trial << " margin=" << best_margin << "\n";
          *out_indices = best_idx;
          return true;
        }
      }
    }
  }

  if (best_margin > 0) {
    if (verbose) std::cout << "    [Extremal] best tet margin=" << best_margin << "\n";
    *out_indices = best_idx;
    return true;
  }
  return false;
}

static double EstimateMaxDescendantMargin(const TriangleQ &tri, const std::vector<vec3> &pts) {
  if (pts.empty()) return -1.0;
  double min_support = 1e30;
  std::mt19937 rng(42);
  std::normal_distribution<double> gauss(0.0, 1.0);
  vec3 worst_u = {0, 0, 0};
  for (int s = 0; s < 2000; s++) {
    vec3 u = {gauss(rng), gauss(rng), gauss(rng)};
    double len = yocto::length(u);
    if (len < 1e-12) continue;
    u = u / len;
    double max_dot = -1e30;
    for (const auto &p : pts) {
      max_dot = std::max(max_dot, yocto::dot(u, p));
    }
    if (max_dot < min_support) {
      min_support = max_dot;
      worst_u = u;
    }
  }
  for (int step = 0; step < 1000; step++) {
    vec3 pert = {gauss(rng) * 0.05, gauss(rng) * 0.05, gauss(rng) * 0.05};
    vec3 u = worst_u + pert;
    double len = yocto::length(u);
    if (len < 1e-12) continue;
    u = u / len;
    double max_dot = -1e30;
    for (const auto &p : pts) {
      max_dot = std::max(max_dot, yocto::dot(u, p));
    }
    if (max_dot < min_support) {
      min_support = max_dot;
      worst_u = u;
    }
  }
  if (min_support <= 0) return 0.0;

  vec3 c0 = ToDouble(tri.corners[0]);
  vec3 c1 = ToDouble(tri.corners[1]);
  vec3 c2 = ToDouble(tri.corners[2]);
  double diam = std::max({yocto::length(c0 - c1), yocto::length(c1 - c2), yocto::length(c2 - c0)});

  // Chebyshev inradius factor: 19/20 * 4/7 = 76/140 = 0.542857.
  // Maximum variation rate: outer_radius * 0.542857 <= 0.95 * 0.542857 <= 0.52.
  return 0.542857 * min_support + 0.52 * diam;
}

static bool SynthesizeCertificate(
    const TriangleQ &tri,
    int depth,
    const BigRat &target_c,
    const BigRat &tube_radius,
    LocalCertificate *out_cert,
    bool verbose = false) {

  vec3 centroid = (ToDouble(tri.corners[0]) + ToDouble(tri.corners[1]) + ToDouble(tri.corners[2])) / 3.0;
  if (verbose) {
    std::cout << "SynthesizeCertificate: depth=" << depth
              << " target_c=" << target_c.ToString()
              << " tube_radius=" << tube_radius.ToString() << "\n"
              << "  centroid=(" << centroid.x << ", " << centroid.y << ", " << centroid.z << ")\n";
  }

  struct Pass {
    int cone_samples;
    bool include_boundaries;
    bool include_corner_cycles;
    double screen_support_error;
  };
  std::vector<Pass> passes;
  passes.push_back({4, false, false, 2e-14});
  if (depth >= 4) {
    passes.push_back({4, true, false, 2e-14});
  }
  if (depth >= 6) {
    passes.push_back({4, true, true, 2e-14});
  }
  if (depth >= 8) {
    passes.push_back({5, true, false, 2e-14});
  }
  if (depth >= 12) {
    passes.push_back({7, true, true, 2e-14});
    passes.push_back({8, true, false, 0.0});
  }
  if (depth >= 16) {
    passes.push_back({8, true, true, 0.0});
    passes.push_back({10, true, true, 0.0});
    passes.push_back({12, true, true, 0.0});
  }

  int pass_num = 0;
  for (const auto &pass : passes) {
    pass_num++;
    std::vector<CandidateTriple> candidates;
    std::vector<vec3> sample_views;
    sample_views.push_back(centroid);
    if (pass.include_corner_cycles) {
      sample_views.push_back(ToDouble(tri.corners[0]));
      sample_views.push_back(ToDouble(tri.corners[1]));
      sample_views.push_back(ToDouble(tri.corners[2]));
    }
    std::set<std::tuple<int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int,int>> seen_cands;
    for (const auto &sv : sample_views) {
      std::vector<CandidateTriple> v_cands;
      GenerateCandidatesForView(sv, tri, pass.cone_samples, pass.include_boundaries, pass.screen_support_error, &v_cands);
      for (const auto &vc : v_cands) {
        auto key = std::make_tuple(
          vc.contacts[0].vertex, vc.contacts[0].edge_start, vc.contacts[0].edge_finish, vc.contacts[0].edge_start2, vc.contacts[0].edge_finish2, vc.contacts[0].mix,
          vc.contacts[1].vertex, vc.contacts[1].edge_start, vc.contacts[1].edge_finish, vc.contacts[1].edge_start2, vc.contacts[1].edge_finish2, vc.contacts[1].mix,
          vc.contacts[2].vertex, vc.contacts[2].edge_start, vc.contacts[2].edge_finish, vc.contacts[2].edge_start2, vc.contacts[2].edge_finish2, vc.contacts[2].mix
        );
        if (seen_cands.insert(key).second) {
          candidates.push_back(vc);
        }
      }
    }
    if (verbose) {
      std::cout << "  Pass " << pass_num << ": candidates=" << candidates.size()
                << " (cone=" << pass.cone_samples << " bdry=" << pass.include_boundaries
                << " corner=" << pass.include_corner_cycles << " err=" << pass.screen_support_error << ")\n";
    }
    if (candidates.size() < 4) continue;

    std::vector<vec3> pts;
    pts.reserve(candidates.size());
    for (const auto &c : candidates) pts.push_back(c.normalized_a);

    if (pass_num >= 2 && depth >= 12) {
      double max_c = EstimateMaxDescendantMargin(tri, pts);
      if (max_c < target_c.ToDouble()) {
        static std::atomic<int> ceiling_reports{0};
        if (ceiling_reports.fetch_add(1) < 20 || verbose) {
          std::cout << AYELLOW("  [MARGIN CEILING DETECTED] depth=") << depth
                    << AYELLOW(" max_achievable_c=") << max_c
                    << AYELLOW(" < target_c=") << target_c.ToDouble()
                    << AYELLOW(" (subdivision cannot reach target_c)") << "\n";
        }
      }
    }

    if (verbose) {
      double min_support_over_sphere = 1e30;
      vec3 worst_u = {0,0,0};
      std::mt19937 rng_check(42);
      std::normal_distribution<double> gauss_check(0.0, 1.0);
      for (int s = 0; s < 50000; s++) {
        vec3 u = {gauss_check(rng_check), gauss_check(rng_check), gauss_check(rng_check)};
        double len = yocto::length(u);
        if (len < 1e-12) continue;
        u = u / len;
        double max_dot = -1e30;
        for (const auto &p : pts) {
          max_dot = std::max(max_dot, yocto::dot(u, p));
        }
        if (max_dot < min_support_over_sphere) {
          min_support_over_sphere = max_dot;
          worst_u = u;
        }
      }
      // Local refinement around worst_u
      for (int step = 0; step < 20000; step++) {
        vec3 pert = {gauss_check(rng_check) * 0.05, gauss_check(rng_check) * 0.05, gauss_check(rng_check) * 0.05};
        vec3 u = worst_u + pert;
        double len = yocto::length(u);
        if (len < 1e-12) continue;
        u = u / len;
        double max_dot = -1e30;
        for (const auto &p : pts) {
          max_dot = std::max(max_dot, yocto::dot(u, p));
        }
        if (max_dot < min_support_over_sphere) {
          min_support_over_sphere = max_dot;
          worst_u = u;
        }
      }
      std::cout << "    TRUE convex hull inradius <= " << min_support_over_sphere
                << " along refined worst_u=(" << worst_u.x << ", " << worst_u.y << ", " << worst_u.z << ")\n";
      int best_worst_u_idx = 0;
      double max_worst_u_dot = -1e30;
      for (size_t i = 0; i < pts.size(); i++) {
        double d = yocto::dot(pts[i], worst_u);
        if (d > max_worst_u_dot) { max_worst_u_dot = d; best_worst_u_idx = i; }
      }
      std::cout << "    Candidate with max dot along worst_u: idx=" << best_worst_u_idx
                << " dot=" << max_worst_u_dot << " pt=(" << pts[best_worst_u_idx].x << ", "
                << pts[best_worst_u_idx].y << ", " << pts[best_worst_u_idx].z << ") supp=("
                << candidates[best_worst_u_idx].contacts[0].vertex << ", "
                << candidates[best_worst_u_idx].contacts[1].vertex << ", "
                << candidates[best_worst_u_idx].contacts[2].vertex << ")\n";
    }

    std::set<int> pool_set;
    std::array<int, 4> best_indices;
    // 0. Extremal regular tetrahedron orientation search
    double min_req_margin = 1.75 * target_c.ToDouble();
    std::array<int, 4> ext_indices;
    if (FindExtremalTetrahedron(pts, min_req_margin, &ext_indices, verbose)) {
      LocalCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = candidates[ext_indices[a]].contacts[0];
        test_cert.axes[a].contacts[1] = candidates[ext_indices[a]].contacts[1];
        test_cert.axes[a].contacts[2] = candidates[ext_indices[a]].contacts[2];
      }
      std::string fail_reason;
      if (ReauditCertificate(tri, test_cert, target_c, tube_radius, out_cert, &fail_reason)) {
        if (verbose) std::cout << "    Extremal tetrahedron SUCCEEDED!\n";
        return true;
      }
      if (verbose) std::cout << "    Extremal tetrahedron failed: " << fail_reason << "\n";
      for (int a = 0; a < 4; a++) pool_set.insert(ext_indices[a]);
    }

    // 1. Deterministic Wolfe balanced tetrahedron search
    bool wolfe_ok = FindBalancedTetrahedron(pts, &best_indices, verbose);
    if (wolfe_ok) {
      LocalCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        test_cert.axes[a].contacts[0] = candidates[best_indices[a]].contacts[0];
        test_cert.axes[a].contacts[1] = candidates[best_indices[a]].contacts[1];
        test_cert.axes[a].contacts[2] = candidates[best_indices[a]].contacts[2];
      }
      std::string fail_reason;
      if (ReauditCertificate(tri, test_cert, target_c, tube_radius, out_cert, &fail_reason)) {
        if (verbose) std::cout << "    Wolfe tetrahedron SUCCEEDED!\n";
        return true;
      }
      if (verbose) std::cout << "    Wolfe tetrahedron failed: " << fail_reason << "\n";
      for (int a = 0; a < 4; a++) pool_set.insert(best_indices[a]);
    }

    // 2. Combinatorial exploration over exposed extreme points
    std::mt19937 rng(1337 + depth * 31);
    std::normal_distribution<double> gauss(0.0, 1.0);
    for (int d = 0; d < 1024; d++) {
      vec3 dir = {gauss(rng), gauss(rng), gauss(rng)};
      int best_hi = 0, best_lo = 0;
      double max_v = yocto::dot(pts[0], dir);
      double min_v = max_v;
      for (size_t i = 1; i < pts.size(); i++) {
        double v = yocto::dot(pts[i], dir);
        if (v > max_v) { max_v = v; best_hi = i; }
        if (v < min_v) { min_v = v; best_lo = i; }
      }
      pool_set.insert(best_hi);
      pool_set.insert(best_lo);
    }
    std::vector<int> pool(pool_set.begin(), pool_set.end());

    struct ScoredTet {
      double margin;
      double slack;
      std::array<int, 4> indices;
    };
    std::vector<ScoredTet> scored;

    int P = pool.size();
    if (P >= 4) {
      uint64_t comb4 = (uint64_t)P * (P - 1) * (P - 2) * (P - 3) / 24;
      if (comb4 <= 100000) {
        for (int i = 0; i < P; i++) {
          for (int j = i + 1; j < P; j++) {
            for (int k = j + 1; k < P; k++) {
              for (int l = k + 1; l < P; l++) {
                vec3 tpts[4] = {pts[pool[i]], pts[pool[j]], pts[pool[k]], pts[pool[l]]};
                double margin;
                double bary[4];
                if (TetrahedronOriginMargin(tpts, &margin, bary)) {
                  double slack = std::min({candidates[pool[i]].strict_slack,
                                           candidates[pool[j]].strict_slack,
                                           candidates[pool[k]].strict_slack,
                                           candidates[pool[l]].strict_slack});
                  scored.push_back({margin, slack, {pool[i], pool[j], pool[k], pool[l]}});
                }
              }
            }
          }
        }
      } else {
        std::uniform_int_distribution<int> dist(0, P - 1);
        for (int trial = 0; trial < 100000; trial++) {
          int i0 = pool[dist(rng)], i1 = pool[dist(rng)], i2 = pool[dist(rng)], i3 = pool[dist(rng)];
          if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
          vec3 tpts[4] = {pts[i0], pts[i1], pts[i2], pts[i3]};
          double margin;
          double bary[4];
          if (TetrahedronOriginMargin(tpts, &margin, bary)) {
            double slack = std::min({candidates[i0].strict_slack,
                                     candidates[i1].strict_slack,
                                     candidates[i2].strict_slack,
                                     candidates[i3].strict_slack});
            scored.push_back({margin, slack, {i0, i1, i2, i3}});
          }
        }
      }
    }

    // 3. Rotated regular tetrahedral frame sampling across ALL candidates
    {
      const vec3 base_dirs[4] = {
        vec3{ 1.0,  1.0,  1.0} / std::sqrt(3.0),
        vec3{ 1.0, -1.0, -1.0} / std::sqrt(3.0),
        vec3{-1.0,  1.0, -1.0} / std::sqrt(3.0),
        vec3{-1.0, -1.0,  1.0} / std::sqrt(3.0),
      };
      std::uniform_real_distribution<double> uangle(0.0,
                                                    2.0 * std::numbers::pi);
      for (int frame = 0; frame < 500; frame++) {
        vec3 axis = {gauss(rng), gauss(rng), gauss(rng)};
        double alen = yocto::length(axis);
        if (alen < 1e-12) continue;
        axis = axis / alen;
        double angle = uangle(rng);
        std::array<int, 4> frame_indices;
        bool valid_frame = true;
        for (int k = 0; k < 4; k++) {
          vec3 v = base_dirs[k];
          vec3 rdir = v * std::cos(angle) + yocto::cross(axis, v) * std::sin(angle) + axis * yocto::dot(axis, v) * (1.0 - std::cos(angle));
          int best_idx = -1;
          double max_d = -1e30;
          for (size_t i = 0; i < pts.size(); i++) {
            double d = yocto::dot(pts[i], rdir);
            if (d > max_d) { max_d = d; best_idx = i; }
          }
          if (best_idx < 0) { valid_frame = false; break; }
          frame_indices[k] = best_idx;
        }
        if (!valid_frame) continue;
        std::sort(frame_indices.begin(), frame_indices.end());
        if (frame_indices[0] == frame_indices[1] || frame_indices[1] == frame_indices[2] || frame_indices[2] == frame_indices[3]) continue;

        vec3 tpts[4] = {pts[frame_indices[0]], pts[frame_indices[1]], pts[frame_indices[2]], pts[frame_indices[3]]};
        double margin;
        double bary[4];
        if (TetrahedronOriginMargin(tpts, &margin, bary)) {
          double slack = std::min({candidates[frame_indices[0]].strict_slack,
                                   candidates[frame_indices[1]].strict_slack,
                                   candidates[frame_indices[2]].strict_slack,
                                   candidates[frame_indices[3]].strict_slack});
          scored.push_back({margin, slack, frame_indices});
        }
      }
    }

    if (scored.empty() && candidates.size() >= 4) {
      std::uniform_int_distribution<int> dist_all(0, candidates.size() - 1);
      for (int trial = 0; trial < 20000; trial++) {
        int i0 = dist_all(rng), i1 = dist_all(rng), i2 = dist_all(rng), i3 = dist_all(rng);
        if (i0 == i1 || i0 == i2 || i0 == i3 || i1 == i2 || i1 == i3 || i2 == i3) continue;
        vec3 tpts[4] = {pts[i0], pts[i1], pts[i2], pts[i3]};
        double margin;
        double bary[4];
        if (TetrahedronOriginMargin(tpts, &margin, bary)) {
          double slack = std::min({candidates[i0].strict_slack,
                                   candidates[i1].strict_slack,
                                   candidates[i2].strict_slack,
                                   candidates[i3].strict_slack});
          scored.push_back({margin, slack, {i0, i1, i2, i3}});
        }
      }
    }

    if (verbose) {
      std::cout << "    Pool size: " << pool.size() << ", Scored tetrahedra: " << scored.size() << "\n";
    }

    std::sort(scored.begin(), scored.end(), [](const ScoredTet &a, const ScoredTet &b) {
      if (a.margin != b.margin) return a.margin > b.margin;
      return a.slack > b.slack;
    });

    int num_to_audit = verbose ? std::min((int)scored.size(), 100) : std::min((int)scored.size(), 20);
    for (int idx = 0; idx < num_to_audit; idx++) {
      LocalCertificate test_cert;
      for (int a = 0; a < 4; a++) {
        int cand_idx = scored[idx].indices[a];
        test_cert.axes[a].contacts[0] = candidates[cand_idx].contacts[0];
        test_cert.axes[a].contacts[1] = candidates[cand_idx].contacts[1];
        test_cert.axes[a].contacts[2] = candidates[cand_idx].contacts[2];
      }
      std::string fail_reason;
      if (ReauditCertificate(tri, test_cert, target_c, tube_radius, out_cert, &fail_reason)) {
        if (verbose) std::cout << "    Scored tet [" << idx << "] SUCCEEDED!\n";
        return true;
      }
      if (verbose && idx < 5) {
        std::cout << "    Scored tet [" << idx << "] margin=" << scored[idx].margin
                  << " slack=" << scored[idx].slack << " failed: " << fail_reason << "\n";
        for (int a = 0; a < 4; a++) {
          int cand_idx = scored[idx].indices[a];
          std::cout << "      Axis " << a << ": supp=("
                    << candidates[cand_idx].contacts[0].vertex << ", "
                    << candidates[cand_idx].contacts[1].vertex << ", "
                    << candidates[cand_idx].contacts[2].vertex << ") pt=("
                    << candidates[cand_idx].normalized_a.x << ", "
                    << candidates[cand_idx].normalized_a.y << ", "
                    << candidates[cand_idx].normalized_a.z << ")\n";
        }
      }
    }
  }

  return false;
}

// Thread-safe Ring Buffer Cache of recent successful certificates
class CertificateCache {
 public:
  void Insert(const LocalCertificate &cert) {
    std::lock_guard<std::mutex> lock(mu_);
    if (certs_.size() < kCapacity) {
      certs_.push_back(cert);
    } else {
      certs_[idx_] = cert;
      idx_ = (idx_ + 1) % kCapacity;
    }
  }

  std::vector<LocalCertificate> GetRecent() const {
    std::lock_guard<std::mutex> lock(mu_);
    return certs_;
  }

 private:
  static constexpr size_t kCapacity = 64;
  mutable std::mutex mu_;
  std::vector<LocalCertificate> certs_;
  size_t idx_ = 0;
};

// Tree node structures
enum class RowKind { SPLIT, LOCAL };

struct Row {
  int id = -1;
  RowKind kind = RowKind::SPLIT;
  int root = 0;
  int depth = 0;
  TriangleQ tri;
  int children[4] = {-1, -1, -1, -1};
  LocalCertificate cert;
};

struct SearchStackItem {
  int id;
  TriangleQ tri;
  int depth;
};

// Application Manager
class TubeCertManager {
 public:
  int initial_child = 0;
  int max_depth = 28;
  int max_nodes = 500000;
  int num_workers = 8;
  int checkpoint_every = 500;
  int chunk_size = 25000; // 0 = single monolithic file
  BigRat target_c = BigRat("5/1000000");
  BigRat tube_radius = BigRat("1/100000");
  std::string output_path = ".artifacts/nopert229/local-view-child0.json";
  std::string progress_log_path = "";
  std::string emit_pack_path = "";
  bool resume = true;

  CertificateCache cache;
  std::mutex tree_mu;
  std::condition_variable cv;
  std::vector<bool> chunk_dirty;
  std::vector<Row> rows;
  std::vector<SearchStackItem> stack;
  std::vector<SearchStackItem> failures;

  void MarkChunkDirty(size_t row_id) {
    if (chunk_size <= 0) return;
    size_t c = row_id / chunk_size;
    if (c >= chunk_dirty.size()) {
      chunk_dirty.resize(c + 1, true);
    }
    chunk_dirty[c] = true;
  }

  std::atomic<int64_t> count_split{0};
  std::atomic<int64_t> count_cert{0};
  std::atomic<int64_t> count_cache_hit{0};
  std::atomic<int64_t> count_synthesized{0};

  bool LoadCheckpoint();
  void SaveCheckpoint(bool complete);
  void Run();
};

static inline int GetIntOrString(const rapidjson::Value &v) {
  if (v.IsInt()) return v.GetInt();
  if (v.IsString()) return std::atoi(v.GetString());
  if (v.IsInt64()) return static_cast<int>(v.GetInt64());
  if (v.IsUint()) return static_cast<int>(v.GetUint());
  if (v.IsUint64()) return static_cast<int>(v.GetUint64());
  return 0;
}

bool TubeCertManager::LoadCheckpoint() {
  if (!resume || !std::filesystem::exists(output_path)) return false;
  std::cout << ACYAN("Loading checkpoint from ") << output_path << "..." << std::flush;
  std::string content = Util::ReadFile(output_path);
  if (content.empty()) return false;

  rapidjson::Document doc;
  doc.Parse(content.c_str());
  if (doc.HasParseError()) {
    std::cerr << ARED("JSON parse error: ") << rapidjson::GetParseError_En(doc.GetParseError()) << "\n";
    return false;
  }

  if (doc.HasMember("target_c")) {
    BigRat cp_target_c(doc["target_c"].GetString());
    if (cp_target_c != target_c) {
      std::cout << AYELLOW("Note: checkpoint target_c (") << cp_target_c.ToString()
                << AYELLOW(") differs from requested (") << target_c.ToString() << ")\n";
    }
  }
  if (doc.HasMember("tube_radius")) {
    BigRat cp_tube_radius(doc["tube_radius"].GetString());
    if (cp_tube_radius != tube_radius) {
      std::cout << AYELLOW("Note: checkpoint tube_radius (") << cp_tube_radius.ToString()
                << AYELLOW(") differs from requested (") << tube_radius.ToString() << ")\n";
    }
  }

  // Load rows either directly from "rows" or from "chunks"
  std::vector<std::string> chunk_files;
  if (doc.HasMember("chunks") && doc["chunks"].IsArray()) {
    std::filesystem::path base_dir = std::filesystem::path(output_path).parent_path();
    for (const auto &c : doc["chunks"].GetArray()) {
      chunk_files.push_back((base_dir / c.GetString()).string());
    }
  }

  size_t row_slot = 0;
  auto parse_row = [&](const rapidjson::Value &val) {
    size_t slot = row_slot++;
    if (slot >= rows.size()) rows.resize(slot + 1);
    if (val.IsNull() || !val.IsObject()) {
      return;
    }
    Row r;
    r.id = GetIntOrString(val["id"]);
    r.depth = GetIntOrString(val["depth"]);
    r.root = val.HasMember("root") ? GetIntOrString(val["root"]) : 0;
    std::string_view kind = val["kind"].GetString();
    const auto &tri_arr = val["triangle"].GetArray();
    for (int i = 0; i < 3; i++) {
      r.tri.corners[i] = BigVecQ3(tri_arr[i][0].GetString(), tri_arr[i][1].GetString(), tri_arr[i][2].GetString());
    }

    if (kind == "view_split") {
      r.kind = RowKind::SPLIT;
      const auto &ch = val["children"].GetArray();
      for (int i = 0; i < 4; i++) r.children[i] = GetIntOrString(ch[i]);
      count_split++;
    } else if (kind == "view_local") {
      r.kind = RowKind::LOCAL;
      r.cert.c = BigRat(val["c"].GetString());
      r.cert.delta = BigRat(val["delta"].GetString());
      r.cert.r = BigRat(val["r"].GetString());
      r.cert.symmetry_index = val.HasMember("symmetry_index") ? GetIntOrString(val["symmetry_index"]) : 0;
      const auto &c_arr = val["certificate"].GetArray();
      for (int a = 0; a < 4; a++) {
        const auto &ax = c_arr[a];
        r.cert.axes[a].B = BigRat(ax["B"].GetString());
        for (int m = 0; m < 3; m++) {
          r.cert.axes[a].contacts[m].edge_start = GetIntOrString(ax["edge_start"][m]);
          r.cert.axes[a].contacts[m].edge_finish = GetIntOrString(ax["edge_finish"][m]);
          r.cert.axes[a].contacts[m].edge_start2 = GetIntOrString(ax["edge_start2"][m]);
          r.cert.axes[a].contacts[m].edge_finish2 = GetIntOrString(ax["edge_finish2"][m]);
          r.cert.axes[a].contacts[m].mix = GetIntOrString(ax["mix"][m]);
          r.cert.axes[a].contacts[m].vertex = GetIntOrString(ax["support_index"][m]);
          r.cert.axes[a].nonzero_witness[m] = GetIntOrString(ax["nonzero_witness"][m]);
        }
      }
      count_cert++;
      cache.Insert(r.cert);
    }
    if (r.id >= (int)rows.size()) rows.resize(r.id + 1);
    rows[r.id] = r;
  };

  if (!chunk_files.empty()) {
    for (size_t chunk_idx = 0; chunk_idx < chunk_files.size(); chunk_idx++) {
      const auto &chunk_path = chunk_files[chunk_idx];
      std::string chunk_content = Util::ReadFile(chunk_path);
      rapidjson::Document chunk_doc;
      chunk_doc.Parse(chunk_content.c_str());
      if (chunk_doc.IsArray()) {
        const auto &arr = chunk_doc.GetArray();
        for (const auto &v : arr) parse_row(v);
        if (chunk_size > 0 && arr.Size() < (size_t)chunk_size) {
          MarkChunkDirty(chunk_idx * chunk_size);
        }
      }
    }
  } else if (doc.HasMember("rows") && doc["rows"].IsArray()) {
    for (const auto &v : doc["rows"].GetArray()) parse_row(v);
  }

  // Load pending stack
  if (doc.HasMember("pending") && doc["pending"].IsArray()) {
    for (const auto &item : doc["pending"].GetArray()) {
      SearchStackItem s;
      s.id = GetIntOrString(item[0]);
      const auto &tri_arr = item[1].GetArray();
      for (int i = 0; i < 3; i++) {
        s.tri.corners[i] = BigVecQ3(tri_arr[i][0].GetString(), tri_arr[i][1].GetString(), tri_arr[i][2].GetString());
      }
      s.depth = GetIntOrString(item[2]);
      stack.push_back(s);
    }
  }

  // Also reload any prior failures onto the search stack so they can be re-evaluated under target_c
  if (doc.HasMember("failures") && doc["failures"].IsArray()) {
    for (const auto &item : doc["failures"].GetArray()) {
      SearchStackItem s;
      if (item.IsObject()) {
        s.id = GetIntOrString(item["id"]);
        const auto &tri_arr = item["triangle"].GetArray();
        for (int i = 0; i < 3; i++) {
          s.tri.corners[i] = BigVecQ3(tri_arr[i][0].GetString(), tri_arr[i][1].GetString(), tri_arr[i][2].GetString());
        }
        s.depth = GetIntOrString(item["depth"]);
      } else if (item.IsArray() && item.Size() >= 3) {
        s.id = GetIntOrString(item[0]);
        const auto &tri_arr = item[1].GetArray();
        for (int i = 0; i < 3; i++) {
          s.tri.corners[i] = BigVecQ3(tri_arr[i][0].GetString(), tri_arr[i][1].GetString(), tri_arr[i][2].GetString());
        }
        s.depth = GetIntOrString(item[2]);
      } else {
        continue;
      }
      stack.push_back(s);
    }
  }

  std::cout << " Done. Loaded " << rows.size() << " rows ("
            << count_cert.load() << " certificates, "
            << stack.size() << " pending).\n";
  return true;
}

static void WriteRowJson(std::ostream &out, const Row &r) {
  if (r.id < 0) {
    out << "  null";
  } else if (r.kind == RowKind::SPLIT) {
    out << std::format(
      "  {{\"id\": {}, \"kind\": \"view_split\", \"root\": {}, \"depth\": {}, \"children\": [{}, {}, {}, {}], "
      "\"triangle\": [[\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"]]}}",
      r.id, r.root, r.depth, r.children[0], r.children[1], r.children[2], r.children[3],
      r.tri.corners[0].x.ToString(), r.tri.corners[0].y.ToString(), r.tri.corners[0].z.ToString(),
      r.tri.corners[1].x.ToString(), r.tri.corners[1].y.ToString(), r.tri.corners[1].z.ToString(),
      r.tri.corners[2].x.ToString(), r.tri.corners[2].y.ToString(), r.tri.corners[2].z.ToString());
  } else {
    out << std::format(
      "  {{\"id\": {}, \"kind\": \"view_local\", \"root\": {}, \"depth\": {}, \"symmetry_index\": {}, "
      "\"r\": \"{}\", \"c\": \"{}\", \"delta\": \"{}\", "
      "\"triangle\": [[\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"]], \"certificate\": [\n",
      r.id, r.root, r.depth, r.cert.symmetry_index,
      r.cert.r.ToString(), r.cert.c.ToString(), r.cert.delta.ToString(),
      r.tri.corners[0].x.ToString(), r.tri.corners[0].y.ToString(), r.tri.corners[0].z.ToString(),
      r.tri.corners[1].x.ToString(), r.tri.corners[1].y.ToString(), r.tri.corners[1].z.ToString(),
      r.tri.corners[2].x.ToString(), r.tri.corners[2].y.ToString(), r.tri.corners[2].z.ToString());
    for (int a = 0; a < 4; a++) {
      const auto &ax = r.cert.axes[a];
      out << std::format(
        "    {{\"edge_start\": [{}, {}, {}], \"edge_finish\": [{}, {}, {}], "
        "\"edge_start2\": [{}, {}, {}], \"edge_finish2\": [{}, {}, {}], "
        "\"mix\": [{}, {}, {}], \"support_index\": [{}, {}, {}], "
        "\"nonzero_witness\": [{}, {}, {}], \"B\": \"{}\"}}{}",
        ax.contacts[0].edge_start, ax.contacts[1].edge_start, ax.contacts[2].edge_start,
        ax.contacts[0].edge_finish, ax.contacts[1].edge_finish, ax.contacts[2].edge_finish,
        ax.contacts[0].edge_start2, ax.contacts[1].edge_start2, ax.contacts[2].edge_start2,
        ax.contacts[0].edge_finish2, ax.contacts[1].edge_finish2, ax.contacts[2].edge_finish2,
        ax.contacts[0].mix, ax.contacts[1].mix, ax.contacts[2].mix,
        ax.contacts[0].vertex, ax.contacts[1].vertex, ax.contacts[2].vertex,
        ax.nonzero_witness[0], ax.nonzero_witness[1], ax.nonzero_witness[2],
        ax.B.ToString(), (a < 3 ? ",\n" : "\n  ]}"));
    }
  }
}

void TubeCertManager::SaveCheckpoint(bool complete) {
  std::lock_guard<std::mutex> lock(tree_mu);
  std::filesystem::path out_file(output_path);
  std::filesystem::path base_dir = out_file.parent_path();
  if (!base_dir.empty() && !std::filesystem::exists(base_dir)) {
    std::filesystem::create_directories(base_dir);
  }
  std::string stem = out_file.stem().string();

  std::vector<std::string> chunk_names;
  if (chunk_size > 0) {
    // Write in chunks
    size_t num_chunks = (rows.size() + chunk_size - 1) / chunk_size;
    if (chunk_dirty.size() < num_chunks) chunk_dirty.resize(num_chunks, true);
    for (size_t chunk_idx = 0; chunk_idx < num_chunks; chunk_idx++) {
      std::string chunk_name = std::format("{}.chunk{:03d}.json", stem, chunk_idx);
      std::filesystem::path chunk_full_path = base_dir / chunk_name;
      chunk_names.push_back(chunk_name);

      bool is_last_chunk = (chunk_idx + 1 == num_chunks);
      bool need_write = complete || is_last_chunk || chunk_dirty[chunk_idx] || !std::filesystem::exists(chunk_full_path);
      if (need_write) {
        size_t start = chunk_idx * chunk_size;
        size_t end = std::min(rows.size(), (chunk_idx + 1) * chunk_size);

        std::string chunk_tmp = chunk_full_path.string() + ".tmp";
        std::ofstream chunk_out(chunk_tmp);
        chunk_out << "[\n";
        for (size_t i = start; i < end; i++) {
          WriteRowJson(chunk_out, rows[i]);
          if (i + 1 < end) chunk_out << ",\n";
          else chunk_out << "\n";
        }
        chunk_out << "]\n";
        chunk_out.close();
        std::filesystem::rename(chunk_tmp, chunk_full_path);
        if (end - start == (size_t)chunk_size || complete) {
          chunk_dirty[chunk_idx] = false;
        }
      }
    }
  }

  // Write manifest
  std::string manifest_tmp = output_path + ".tmp";
  std::ofstream out(manifest_tmp);
  out << "{\n"
      << "  \"complete\": " << (complete ? "true" : "false") << ",\n"
      << "  \"target_c\": \"" << target_c.ToString() << "\",\n"
      << "  \"tube_radius\": \"" << tube_radius.ToString() << "\",\n"
      << "  \"max_depth\": " << max_depth << ",\n"
      << "  \"initial_child\": " << initial_child << ",\n";

  if (chunk_size > 0) {
    out << "  \"chunks\": [\n";
    for (size_t i = 0; i < chunk_names.size(); i++) {
      out << "    \"" << chunk_names[i] << "\"" << (i + 1 < chunk_names.size() ? ",\n" : "\n");
    }
    out << "  ],\n";
  } else {
    out << "  \"rows\": [\n";
    for (size_t i = 0; i < rows.size(); i++) {
      WriteRowJson(out, rows[i]);
      if (i + 1 < rows.size()) out << ",\n";
      else out << "\n";
    }
    out << "  ],\n";
  }

  out << "  \"pending\": [\n";
  for (size_t i = 0; i < stack.size(); i++) {
    const auto &s = stack[i];
    out << std::format("    [{}, [[\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"]], {}]{}\n",
                       s.id,
                       s.tri.corners[0].x.ToString(), s.tri.corners[0].y.ToString(), s.tri.corners[0].z.ToString(),
                       s.tri.corners[1].x.ToString(), s.tri.corners[1].y.ToString(), s.tri.corners[1].z.ToString(),
                       s.tri.corners[2].x.ToString(), s.tri.corners[2].y.ToString(), s.tri.corners[2].z.ToString(),
                       s.depth, (i + 1 < stack.size() ? "," : ""));
  }
  out << "  ],\n";

  out << "  \"counts\": {\n"
      << "    \"view_split\": " << count_split.load() << ",\n"
      << "    \"certificate\": " << count_cert.load() << ",\n"
      << "    \"nearby_reused_certificates\": " << count_cache_hit.load() << ",\n"
      << "    \"synthesized_certificates\": " << count_synthesized.load() << "\n"
      << "  },\n";

  out << "  \"failures\": [\n";
  for (size_t i = 0; i < failures.size(); i++) {
    const auto &f = failures[i];
    out << std::format("    [{}, [[\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"], [\"{}\", \"{}\", \"{}\"]], {}]{}\n",
                       f.id,
                       f.tri.corners[0].x.ToString(), f.tri.corners[0].y.ToString(), f.tri.corners[0].z.ToString(),
                       f.tri.corners[1].x.ToString(), f.tri.corners[1].y.ToString(), f.tri.corners[1].z.ToString(),
                       f.tri.corners[2].x.ToString(), f.tri.corners[2].y.ToString(), f.tri.corners[2].z.ToString(),
                       f.depth, (i + 1 < failures.size() ? "," : ""));
  }
  out << "  ]\n";
  out << "}\n";
  out.close();
  std::filesystem::rename(manifest_tmp, output_path);

  double uncertified = 0.0;
  for (const auto &s : stack) uncertified += std::pow(4.0, -(s.depth - 1));
  for (const auto &f : failures) uncertified += std::pow(4.0, -(f.depth - 1));
  double certified_pct = complete ? 100.0 : std::max(0.0, std::min(100.0, (1.0 - uncertified) * 100.0));

  std::cout << std::format("Checkpoint saved: rows={}, pending={}, certs={}, cache_hits={}, synth={}, certified={:.3f}%\n",
                           rows.size(), stack.size(), count_cert.load(), count_cache_hit.load(), count_synthesized.load(), certified_pct)
            << std::flush;

  std::string log_path = progress_log_path;
  if (log_path.empty() && !output_path.empty()) {
    log_path = std::filesystem::path(output_path).replace_extension(".log").string();
  }
  if (!log_path.empty()) {
    std::filesystem::path parent = std::filesystem::path(log_path).parent_path();
    if (!parent.empty() && !std::filesystem::exists(parent)) {
      std::filesystem::create_directories(parent);
    }
    bool is_new = !std::filesystem::exists(log_path) || std::filesystem::file_size(log_path) == 0;
    std::ofstream log_out(log_path, std::ios::app);
    if (log_out.is_open()) {
      if (is_new) {
        log_out << "# timestamp certs certified_pct\n";
      }
      time_t now = time(nullptr);
      log_out << std::format("{} {} {:.8f}\n", (int64_t)now, count_cert.load(), certified_pct) << std::flush;
    }
  }
}

void TubeCertManager::Run() {
  // If stack is empty, initialize root
  if (stack.empty() && rows.empty()) {
    TriangleQ wedge;
    wedge.corners[0] = BigVecQ3(BigRat(1), BigRat(0), BigRat(0));
    wedge.corners[1] = BigVecQ3(BigRat(10, 41), BigRat(31, 41), BigRat(0));
    wedge.corners[2] = BigVecQ3(BigRat(0), BigRat(0), BigRat(1));

    TriangleQ children[4];
    wedge.Subdivide(children);

    Row root_row;
    root_row.id = 0;
    root_row.kind = RowKind::SPLIT;
    root_row.depth = 1;
    root_row.root = 0;
    root_row.tri = children[initial_child];
    root_row.children[0] = 1;
    root_row.children[1] = 2;
    root_row.children[2] = 3;
    root_row.children[3] = 4;
    rows.push_back(root_row);
    rows.resize(5); // allocate slots 1, 2, 3, 4
    MarkChunkDirty(0);
    MarkChunkDirty(4);

    TriangleQ sub[4];
    root_row.tri.Subdivide(sub);
    for (int i = 0; i < 4; i++) {
      stack.push_back({i + 1, sub[i], 2});
    }
  }

  std::cout << ACYAN("Starting C++ Identity Tube Search on ") << num_workers << " threads...\n"
            << "Tube radius: " << tube_radius.ToString() << "\n"
            << "Target margin c: " << target_c.ToString() << "\n"
            << "Max depth: " << max_depth << "\n\n" << std::flush;

  SaveCheckpoint(false);

  std::atomic<bool> done{false};
  std::atomic<int> active_workers{num_workers};
  std::atomic<int64_t> total_processed{0};

  auto worker_func = [&](int tid) {
    while (!done.load()) {
      SearchStackItem item;
      {
        std::unique_lock<std::mutex> lock(tree_mu);
        while (stack.empty()) {
          active_workers--;
          if (active_workers.load() == 0 && stack.empty()) {
            done = true;
            cv.notify_all();
            return;
          }
          cv.wait_for(lock, std::chrono::milliseconds(50), [&] {
            return done.load() || !stack.empty();
          });
          if (done.load() && stack.empty()) {
            return;
          }
          active_workers++;
        }
        item = stack.back();
        stack.pop_back();
      }

      // Process item
      LocalCertificate certified;
      bool success = false;

      // 1. Check recent cached certificates (gives >95% hits in DFS)
      std::vector<LocalCertificate> recent = cache.GetRecent();
      for (const auto &c : recent) {
        if (ReauditCertificate(item.tri, c, target_c, tube_radius, &certified)) {
          success = true;
          count_cache_hit++;
          break;
        }
      }

      // 2. If cache missed, synthesize new candidate certificate
      if (!success) {
        if (SynthesizeCertificate(item.tri, item.depth, target_c, tube_radius, &certified)) {
          success = true;
          count_synthesized++;
        }
      }

      if (success) {
        std::lock_guard<std::mutex> lock(tree_mu);
        Row r;
        r.id = item.id;
        r.kind = RowKind::LOCAL;
        r.depth = item.depth;
        r.root = 0;
        r.tri = item.tri;
        r.cert = certified;
        if (item.id >= (int)rows.size()) rows.resize(item.id + 1);
        rows[item.id] = r;
        MarkChunkDirty(item.id);
        count_cert++;
        cache.Insert(certified);
      } else {
        // Need to subdivide or fail
        if (item.depth >= max_depth) {
          std::lock_guard<std::mutex> lock(tree_mu);
          failures.push_back(item);
        } else {
          TriangleQ sub[4];
          item.tri.Subdivide(sub);
          int new_ids[4];
          {
            std::lock_guard<std::mutex> lock(tree_mu);
            size_t base = rows.size();
            rows.resize(base + 4);
            for (int i = 0; i < 4; i++) new_ids[i] = base + i;

            Row split_row;
            split_row.id = item.id;
            split_row.kind = RowKind::SPLIT;
            split_row.depth = item.depth;
            split_row.root = 0;
            split_row.tri = item.tri;
            for (int i = 0; i < 4; i++) split_row.children[i] = new_ids[i];
            if (item.id >= (int)rows.size()) rows.resize(item.id + 1);
            rows[item.id] = split_row;
            MarkChunkDirty(item.id);
            MarkChunkDirty(base);
            MarkChunkDirty(base + 3);
            count_split++;

            for (int i = 3; i >= 0; i--) {
              stack.push_back({new_ids[i], sub[i], item.depth + 1});
            }
            cv.notify_all();
          }
        }
      }

      int64_t cur = ++total_processed;
      if (max_nodes > 0 && cur >= max_nodes) {
        done = true;
        cv.notify_all();
        break;
      }
      static std::atomic<time_t> last_checkpoint_time{time(nullptr)};
      time_t now = time(nullptr);
      bool time_to_checkpoint = (checkpoint_every > 0 && cur % checkpoint_every == 0);
      if (!time_to_checkpoint && (now - last_checkpoint_time.load() >= 30)) {
        time_t last = last_checkpoint_time.load();
        if (now - last >= 30) {
          if (last_checkpoint_time.compare_exchange_strong(last, now)) {
            time_to_checkpoint = true;
          }
        }
      }
      if (time_to_checkpoint) {
        last_checkpoint_time.store(now);
        SaveCheckpoint(false);
      }
    }
    active_workers--;
  };

  std::vector<std::thread> threads;
  for (int i = 0; i < num_workers; i++) {
    threads.emplace_back(worker_func, i);
  }

  for (auto &t : threads) {
    if (t.joinable()) t.join();
  }

  bool complete = stack.empty() && failures.empty();
  if (complete) {
    for (const auto &r : rows) {
      if (r.id < 0) {
        complete = false;
        break;
      }
    }
  }
  SaveCheckpoint(complete);

  std::cout << AGREEN("\nSearch completed! ")
            << "Final rows: " << rows.size()
            << ", Certificates: " << count_cert.load()
            << ", Failures: " << failures.size() << "\n";
}

#ifndef TUBECERT_NO_MAIN
int main(int argc, char **argv) {
  TubeCertManager mgr;
  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--initial_child" || arg == "--initial-child") {
      mgr.initial_child = std::atoi(argv[++i]);
    } else if (arg == "--tube_radius" || arg == "--tube-radius") {
      mgr.tube_radius = BigRat(argv[++i]);
    } else if (arg == "--target_c" || arg == "--target-c") {
      mgr.target_c = BigRat(argv[++i]);
    } else if (arg == "--max_depth" || arg == "--max-depth") {
      mgr.max_depth = std::atoi(argv[++i]);
    } else if (arg == "--max_nodes" || arg == "--max-nodes") {
      mgr.max_nodes = std::atoi(argv[++i]);
    } else if (arg == "--workers" || arg == "--threads") {
      mgr.num_workers = std::atoi(argv[++i]);
    } else if (arg == "--output" || arg == "-o") {
      mgr.output_path = argv[++i];
    } else if (arg == "--log" || arg == "--progress_log" || arg == "--progress-log") {
      mgr.progress_log_path = argv[++i];
    } else if (arg == "--chunk_size" || arg == "--chunk-size") {
      mgr.chunk_size = std::atoi(argv[++i]);
    } else if (arg == "--checkpoint_every" || arg == "--checkpoint-every") {
      mgr.checkpoint_every = std::atoi(argv[++i]);
    } else if (arg == "--emit_pack" || arg == "--emit-pack") {
      mgr.emit_pack_path = argv[++i];
    } else if (arg == "--resume") {
      mgr.resume = true;
    } else if (arg == "--fresh") {
      mgr.resume = false;
    } else if (arg == "--test_f0") {
      std::string path = "Noperthedron/.artifacts/nopert229/local-view-child0.json.before-cpp.bak";
      if (i + 1 < argc && argv[i + 1][0] != '-') {
        path = argv[++i];
      }
      if (!std::filesystem::exists(path)) {
        if (std::filesystem::exists("../" + path)) {
          path = "../" + path;
        } else if (std::filesystem::exists("/home/tom/nopert-project/" + path)) {
          path = "/home/tom/nopert-project/" + path;
        }
      }
      std::string s = Util::ReadFile(path);
      if (s.empty()) {
        std::cerr << "Error: cannot read " << path << "\n";
        return 1;
      }
      rapidjson::Document d;
      d.Parse(s.c_str());
      if (!d.IsObject() || !d.HasMember("failures") || !d["failures"].IsArray()) {
        std::cerr << "Error: JSON does not contain valid failures array: " << path << "\n";
        return 1;
      }
      const auto &fails = d["failures"].GetArray();
      std::cout << "Testing " << fails.Size() << " failures from before-cpp.bak:\n";
      int successes = 0;
      for (size_t i = 0; i < fails.Size(); i++) {
        const auto &f = fails[i];
        TriangleQ tri;
        rapidjson::Value::ConstArray tri_arr = f.IsObject() ? f["triangle"].GetArray() : f[1].GetArray();
        for (int k = 0; k < 3; k++) {
          tri.corners[k] = BigVecQ3(tri_arr[k][0].GetString(), tri_arr[k][1].GetString(), tri_arr[k][2].GetString());
        }
        int depth = f.IsObject() ? (f.HasMember("depth") ? f["depth"].GetInt() : 28) : f[2].GetInt();
        int f_id = f.IsObject() ? (f.HasMember("id") ? f["id"].GetInt() : (int)i) : f[0].GetInt();
        LocalCertificate cert;
        bool ok = SynthesizeCertificate(tri, depth, mgr.target_c, mgr.tube_radius, &cert);
        std::cout << "  Failure [" << i << "] id=" << f_id << " d=" << depth << ": " << (ok ? "SUCCESS" : "FAIL") << "\n";
        if (ok) successes++;
      }
      std::cout << "Total failure successes: " << successes << " / " << fails.Size() << "\n";

      if (d.HasMember("pending") && d["pending"].IsArray()) {
        const auto &pend = d["pending"].GetArray();
        int total_pend = pend.Size();
        int pend_success = 0;

        std::map<int, std::pair<int, int>> depth_stats;
        for (size_t i = 0; i < pend.Size(); i++) {
          const auto &p = pend[i];
          int depth = p[2].GetInt();
          TriangleQ tri;
          const auto &tri_arr = p[1].GetArray();
          for (int k = 0; k < 3; k++) {
            tri.corners[k] = BigVecQ3(tri_arr[k][0].GetString(), tri_arr[k][1].GetString(), tri_arr[k][2].GetString());
          }
          LocalCertificate cert;
          bool ok = SynthesizeCertificate(tri, depth, mgr.target_c, mgr.tube_radius, &cert);
          depth_stats[depth].first++;
          if (ok) {
            depth_stats[depth].second++;
            pend_success++;
          }
        }
        std::cout << "Pending breakdown by depth (total: " << pend_success << " / " << total_pend << " direct successes):\n";
        for (const auto &[dep, counts] : depth_stats) {
          std::cout << "  depth " << dep << ": " << counts.second << " / " << counts.first
                    << " (" << (counts.first == counts.second ? "100%" : std::format("{:.1f}%", 100.0 * counts.second / counts.first)) << ")\n";
        }
      }
      return 0;
    } else if (arg == "--diagnose_fail") {
      int fail_idx = 0;
      if (i + 1 < argc && argv[i + 1][0] != '-') {
        fail_idx = std::atoi(argv[++i]);
      }
      std::string path = mgr.output_path;
      if (!std::filesystem::exists(path)) {
        path = "Noperthedron/.artifacts/nopert229/local-view-child0.json";
      }
      if (!std::filesystem::exists(path)) {
        path = ".artifacts/nopert229/local-view-child0.json";
      }
      std::string s = Util::ReadFile(path);
      rapidjson::Document d;
      d.Parse(s.c_str());
      if (d.HasParseError() || !d.IsObject() || !d.HasMember("failures") || !d["failures"].IsArray()) {
        std::cerr << "Failed to load failures from " << path << "\n";
        return 1;
      }
      const auto &fails = d["failures"].GetArray();
      if (fail_idx >= (int)fails.Size()) {
        std::cerr << "fail_idx " << fail_idx << " out of range (" << fails.Size() << " failures)\n";
        return 1;
      }
      const auto &f = fails[fail_idx];
      int f_id = 0, f_depth = 0;
      rapidjson::Value::ConstArray tri_arr = f.IsObject() ? f["triangle"].GetArray() : f[1].GetArray();
      if (f.IsObject()) {
        f_id = f["id"].GetInt();
        f_depth = f["depth"].GetInt();
      } else {
        f_id = f[0].GetInt();
        f_depth = f[2].GetInt();
      }
      std::cout << "Diagnosing failure [" << fail_idx << "] id=" << f_id << " depth=" << f_depth << ":\n";
      TriangleQ tri;
      for (int k = 0; k < 3; k++) {
        tri.corners[k] = BigVecQ3(tri_arr[k][0].GetString(), tri_arr[k][1].GetString(), tri_arr[k][2].GetString());
        std::cout << "  Corner " << k << ": (" << tri.corners[k].x.ToString() << ", "
                  << tri.corners[k].y.ToString() << ", " << tri.corners[k].z.ToString() << ")\n";
      }
      LocalCertificate cert;
      bool ok = SynthesizeCertificate(tri, f_depth, mgr.target_c, mgr.tube_radius, &cert, true);
      std::cout << "Final synthesis result: " << (ok ? "SUCCESS" : "FAIL") << "\n";
      return 0;
    } else if (arg == "--diagnose_node") {
      int node_id = std::atoi(argv[++i]);
      if (mgr.LoadCheckpoint()) {
        if (node_id < 0 || node_id >= (int)mgr.rows.size()) {
          std::cerr << "Node id " << node_id << " not found in rows (size " << mgr.rows.size() << ")\n";
          return 1;
        }
        const auto &r = mgr.rows[node_id];
        std::cout << "Diagnosing node id=" << node_id << " depth=" << r.depth << ":\n";
        for (int k = 0; k < 3; k++) {
          std::cout << "  Corner " << k << ": (" << r.tri.corners[k].x.ToString() << ", "
                    << r.tri.corners[k].y.ToString() << ", " << r.tri.corners[k].z.ToString() << ")\n";
        }
        LocalCertificate cert;
        bool ok = SynthesizeCertificate(r.tri, r.depth, mgr.target_c, mgr.tube_radius, &cert, true);
        std::cout << "Final synthesis result: " << (ok ? "SUCCESS" : "FAIL") << "\n";
        return 0;
      }
    }
  }

  if (mgr.LoadCheckpoint()) {
    std::cout << "Resumed from existing checkpoint.\n";
  }

  mgr.Run();
  return 0;
}
#endif
