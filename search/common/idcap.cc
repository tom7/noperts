// idcap: blow-up certificates at the identity over a view triangle (the
// design: nopert229/notes/DENSE-SPOTS.md). The identity tube (tubecode)
// bounds the second-order terms crudely (radius <= 2 c, c its first-order
// cage margin); where c is small (the Septopert's strip of views near
// (0.9285, 0.3565, 0.1040), c ~ 3e-4) its radius is tiny, although the exact
// balanced witnesses hold much farther out. Here the rotations near the
// identity are blown up and the witnesses checked as polynomials (as the
// snub cube's caps, search/sc/sccapcert.cc; Lean Pipeline/KCapCheck.lean).
//
// For the view triangle T = (c0, c1, c2) (projective chart points) and a
// radius rho, the six charts (axis a, sign s) have variables
// y = (mu, alpha, beta, p1, p2) in [0, rho] x [0, 1]^2 x [-1, 1]^2:
//   view      u = c0 + alpha (c1 - c0) + alpha beta (c2 - c1)  (T as a
//             collapsed square; d_k = u x c_k is perpendicular to u whatever
//             its scale)
//   rotation  Cayley vector w = mu sigma, sigma_a = s, the other two (p1, p2)
// so the six cover every view of T and every Cayley vector with
// |w|_inf <= rho (the ball |w|_2 <= rho, tube radius 2 rho), the identity
// (mu = 0) included.
//
// A leaf is a balanced witness, as sccapcert's: contacts k with edge
// directions c_k = v_b - v_a, weights 1 (a pair, c_1 = -c_0) or the Cramer
// weights s (c_{k+1} x c_{k+2}) . u, outer sets S_k with every other vertex
// dominated, and per tuple j of S_0 x ... the inner choices i_k:
//   P = sum_k lambda_k (N(w) v_{i_k} . d_k - D(w) v_{j_k} . d_k),
// divided by the largest power of mu dividing it, has a nonnegative tensor
// Bernstein bound on the box. With i_k = j_k the mu^0 term vanishes, and
// P / mu is the first-order cage term plus the exact higher-order terms.
//
// So far: the double-precision screen (leaf counts, to size the
// certificate); the exact check and the export follow.
//
// Usage: idcap.exe (--view x,y,z [--size 1e-3] | --code C --tri T [--path D...])
//          [--rho 1/64] [--faces 0:1,...] [--max_depth 40] [--try 16]
//          [--threads 64] [--bdd codebdd.json]
// --view: an equilateral triangle of the given angular diameter around the
// view (as tubeprobe); --code/--tri: code C's triangle T of codebdd.json,
// subdivided along the digits of --path (tubetree::TriangleQ::Subdivide).
// --trees_in DIR --trees_out DIR [--codes C,...] [--pass_depth 6]: the tree
// pass: every code's tube tree (tubecode/tuberefine) with its nodes down to
// --pass_depth replaced by blow-up leaves (Lean Row.idcap; radius rho) where
// they certify and the existing subtree's radius is smaller.
// --double: the double screen only (no exact check).
// --affine [--affine_gap 4]: affine nodes (Lean ATree.affine) where a failing
// tuple's bad region is slanted (an experiment; see SEPTOPERT-IMPROVEMENTS).
// --blend: where no single inner choice certifies a tuple, try points on
// the segment between two inner choices' vertices (Lean KCap.Leaf.blends;
// pack tag 4): where the best inner vertex switches inside a box (a
// codimension-2 view), the blend has no switch to subdivide toward.
// (Blends in the split lookahead too: leaf checks only was worse.)
// --blend_contacts L: also a separate blend per contact (coordinate ascent),
// where several contacts switch independently: L = 1 in the leaf checks,
// 2 also in the split lookahead.
// --code_jobs N: the pass runs N codes at once (largest trees first).
// --probe N: the candidate witnesses' first-order margin at the triangle's
// center over an N x N grid of directions per cube face (no certificate).
// --view_depth D (with --code): a view tree as the identity tube's: each
// node is certified if every face takes at most --max_leaves nodes, else
// split in four, down to D levels below the start.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <execinfo.h>
#include <filesystem>
#include <unistd.h>
#include <functional>
#include <future>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"
#include "base/stringprintf.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "kpoly.h"
#include "model.h"
#include "rapidjson/document.h"
#include "tubetree.h"
#include "util.h"

// Q as a kpoly scalar.
template <> inline bool kpoly::IsZeroT<BigRat>(const BigRat &x) { return x == BigRat(0); }
template <> inline BigRat kpoly::One<BigRat>() { return BigRat(1); }
template <> inline BigRat kpoly::FromQ<BigRat>(const BigRat &q) { return q; }

namespace {

using namespace kpoly;

int g_try = 16;
bool g_exact = true;
// Affine nodes (Lean ATree.affine) where a failing tuple's bad region is
// slanted; at least this many levels apart on a path.
bool g_affine = false;
bool g_blend = false;
// --blend_contacts L: also per-contact blends (coordinate ascent): 1 in the
// leaf checks, 2 also in the split lookahead.
int g_blend_contacts = 0;
// --mu_guard: no mu split where every candidate fails at the box's lowest mu.
bool g_mu_guard = false;
int g_affine_gap = 4;

// ----- Exact bounds over Q (Lean KPoly.lowerDeg with ExactScalarOps Q: lo = the value) -----
struct QOps {
  Q zero() const { return Q(0); }
  Q add(const Q &a, const Q &b) const { return a + b; }
  bool is_zero(const Q &a) const { return a == Q(0); }
  Q scale(const Q &q, const Q &a) const { return q * a; }
};

// The minimum Bernstein coefficient of p on the box is >= 0 (> 0 when
// strict); outward-rounded interval coefficients decide first.
bool ExactLowerOk(const PolyT<Q> &p, const std::array<std::pair<Q, Q>, NV> &box, bool strict) {
  const std::array<int, NV> deg = Degrees(p);
  std::map<Exp, Iv> ti;
  bool any = false;
  for (const auto &[e, c] : p.t) if (!(c == Q(0))) { ti[e] = IvOfQ(c); any = true; }
  if (!any) return !strict;  // the zero polynomial: lowerDeg = 0
  const std::vector<Iv> iv = Bernstein(ti, deg, box, IvOps());
  double m = INFINITY;
  for (const Iv &x : iv) m = std::min(m, x.lo);
  if (strict ? m > 0 : m >= 0) return true;
  std::map<Exp, Q> tq;
  for (const auto &[e, c] : p.t) if (!(c == Q(0))) tq[e] = c;
  for (const Q &x : Bernstein(tq, deg, box, QOps())) {
    const int sg = Q::Sign(x);
    if (strict ? sg <= 0 : sg < 0) return false;
  }
  return true;
}

// Pack tokens (Lean PackedLocalViewTree): a rational as zigzag numerator, denominator.
std::string ZigzagRat(const Q &r) {
  const BigInt num = r.Numerator(), den = r.Denominator();
  const BigInt zz = (num >= 0) ? (num * 2) : ((BigInt(0) - num) * 2 - 1);
  return zz.ToString() + "," + den.ToString();
}

// ----- The solid -----
struct Setup {
  std::vector<V3<Q>> VQ;
  std::vector<V3<double>> V;
  V3<Q> c[3];  // the view triangle (projective chart points)
  Q rho;
};

double Dot(const V3<double> &a, const V3<double> &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
V3<double> Cross(const V3<double> &a, const V3<double> &b) { return VCross(a, b); }
V3<double> Add(const V3<double> &a, const V3<double> &b) { return {a[0] + b[0], a[1] + b[1], a[2] + b[2]}; }
V3<double> Sub(const V3<double> &a, const V3<double> &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
V3<double> Scale(double s, const V3<double> &a) { return {s * a[0], s * a[1], s * a[2]}; }
double Norm(const V3<double> &a) { return std::sqrt(Dot(a, a)); }
V3<double> ToD(const V3<Q> &v) { return {v[0].ToDouble(), v[1].ToDouble(), v[2].ToDouble()}; }

// ----- Charts -----
struct ChartId {
  int axis = 0;
  bool sign = true;
  std::string Name() const { return std::to_string(axis) + ":" + (sign ? "1" : "-1"); }
};

template <class T> T ToT(const Q &x);
template <> double ToT<double>(const Q &x) { return x.ToDouble(); }
template <> Q ToT<Q>(const Q &x) { return x; }
template <class T> V3<T> ToTV(const V3<Q> &v) { return {ToT<T>(v[0]), ToT<T>(v[1]), ToT<T>(v[2])}; }

template <class T> struct Chart { PV<T> u, w; PolyT<T> D; std::vector<PV<T>> NV_; };

// An affine change of the chart variables y = A z + c (Lean KCap.AffMap),
// B = A^-1 exactly; it fixes variable 0 (mu). `ident`: the identity, whose
// chart is built from the variables themselves (the polynomials of a tree
// without affine nodes are exactly as before).
struct AffMapQ {
  bool ident = true;
  std::array<std::array<Q, NV>, NV> A, B;
  std::array<Q, NV> c;
  static AffMapQ Identity() {
    AffMapQ m;
    for (int i = 0; i < NV; i++) {
      for (int j = 0; j < NV; j++) m.A[i][j] = m.B[i][j] = Q(i == j ? 1 : 0);
      m.c[i] = Q(0);
    }
    return m;
  }
};

// The exact inverse of a matrix (Gauss-Jordan); false if singular.
bool Invert(const std::array<std::array<Q, NV>, NV> &M, std::array<std::array<Q, NV>, NV> *out) {
  std::array<std::array<Q, 2 * NV>, NV> a;
  for (int i = 0; i < NV; i++)
    for (int j = 0; j < 2 * NV; j++) a[i][j] = j < NV ? M[i][j] : Q(j - NV == i ? 1 : 0);
  for (int col = 0; col < NV; col++) {
    int piv = -1;
    for (int r = col; r < NV; r++) if (!(a[r][col] == Q(0))) { piv = r; break; }
    if (piv < 0) return false;
    std::swap(a[col], a[piv]);
    const Q inv = Q(1) / a[col][col];
    for (int j = 0; j < 2 * NV; j++) a[col][j] = a[col][j] * inv;
    for (int r = 0; r < NV; r++) {
      if (r == col || a[r][col] == Q(0)) continue;
      const Q f = a[r][col];
      for (int j = 0; j < 2 * NV; j++) a[r][j] = a[r][j] - f * a[col][j];
    }
  }
  for (int i = 0; i < NV; i++)
    for (int j = 0; j < NV; j++) (*out)[i][j] = a[i][NV + j];
  return true;
}

// A double rounded to a multiple of 2^-bits (exactly representable).
double RoundDyadic(double x, int bits) { return std::ldexp(std::round(std::ldexp(x, bits)), -bits); }
double FloorDyadic(double x, int bits) { return std::ldexp(std::floor(std::ldexp(x, bits)), -bits); }
double CeilDyadic(double x, int bits) { return std::ldexp(std::ceil(std::ldexp(x, bits)), -bits); }

template <class T> Chart<T> MakeChart(const Setup &st, const ChartId &id,
                                        const AffMapQ &map = AffMapQ::Identity()) {
  using P = PolyT<T>;
  // The chart variables as polynomials in the tree's coordinates (Lean AffMap.vars).
  std::array<P, NV> v;
  for (int i = 0; i < NV; i++) {
    if (map.ident) { v[i] = P::Var(i); continue; }
    P s = P::Const(FromQ<T>(map.c[i]));
    for (int j = 0; j < NV; j++)
      if (!(map.A[i][j] == Q(0))) s = s + FromQ<T>(map.A[i][j]) * P::Var(j);
    v[i] = s;
  }
  const V3<T> c0 = ToTV<T>(st.c[0]), c1 = ToTV<T>(st.c[1]), c2 = ToTV<T>(st.c[2]);
  Chart<T> ch;
  ch.u = PConst(c0) + (v[1] * PConst(VSub(c1, c0)) + (v[1] * v[2]) * PConst(VSub(c2, c1)));
  PV<T> sigma;
  int free = 3;
  for (int i = 0; i < 3; i++)
    sigma[i] = i == id.axis ? P::Const(FromQ<T>(Q(id.sign ? 1 : -1))) : v[free++];
  ch.w = v[0] * sigma;
  const P ww = PDot(ch.w, ch.w);
  ch.D = P::Const(One<T>()) + ww;
  for (const V3<Q> &vq : st.VQ) {
    const PV<T> cv = PConst(ToTV<T>(vq));
    // N(w) v = (1 - |w|^2) v + 2 (w.v) w + 2 w x v (Lean cayleyNum).
    const P two = P::Const(One<T>() + One<T>());
    ch.NV_.push_back((P::Const(One<T>()) - ww) * cv + ((two * PDot(ch.w, cv)) * ch.w + two * PCross(ch.w, cv)));
  }
  return ch;
}

Box ChartBox(const Setup &st) {
  return {std::make_pair(0.0, st.rho.ToDouble()), std::make_pair(0.0, 1.0), std::make_pair(0.0, 1.0),
          std::make_pair(-1.0, 1.0), std::make_pair(-1.0, 1.0)};
}

// ----- Poses and witnesses (double) -----
struct Pose { V3<double> u, w; };
Pose PoseAt(const Chart<double> &ch, const double *y) {
  Pose q;
  for (int a = 0; a < 3; a++) { q.u[a] = Eval(ch.u[a], y); q.w[a] = Eval(ch.w[a], y); }
  return q;
}
V3<double> Rot(const V3<double> &w, const V3<double> &v) {
  const double ww = Dot(w, w);
  const V3<double> wv = Cross(w, v);
  V3<double> r;
  for (int a = 0; a < 3; a++) r[a] = ((1 - ww) * v[a] + 2 * w[a] * Dot(w, v) + 2 * wv[a]) / (1 + ww);
  return r;
}

// A contact: the edge direction c = V[b] - V[a], its support set at the
// reference view (the vertices maximal along u x c), its best inner vertex.
struct Contact { int a = 0, b = 0, i = 0; V3<double> c; std::vector<int> S; };
struct Witness { std::vector<Contact> k; int s = 1; };

std::vector<int> SupportSet(const Setup &st, const V3<double> &d) {
  double h = -1e300;
  for (const auto &v : st.V) h = std::max(h, Dot(v, d));
  std::vector<int> S;
  for (int j = 0; j < (int)st.V.size(); j++) if (Dot(st.V[j], d) >= h - 1e-9 * Norm(d)) S.push_back(j);
  return S;
}

std::vector<double> Weights(const Witness &W, const Pose &q) {
  if (W.k.size() == 2) return {1, 1};
  std::vector<double> l(3);
  for (int k = 0; k < 3; k++) l[k] = W.s * Dot(Cross(W.k[(k + 1) % 3].c, W.k[(k + 2) % 3].c), q.u);
  return l;
}

// The witness's normalized value at a pose (>= 0: the pose is excluded).
double Value(const Setup &st, const Witness &W, const Pose &q) {
  const std::vector<double> l = Weights(W, q);
  double sl = 0;
  for (double x : l) { if (x < 0) return -1e300; sl += x; }
  if (sl <= 0) return -1e300;
  double s = 0;
  for (size_t k = 0; k < W.k.size(); k++) {
    const Contact &c = W.k[k];
    const V3<double> d = Cross(q.u, c.c);
    double h = -1e300, best = -1e300;
    for (const auto &v : st.V) h = std::max(h, Dot(v, d));
    for (const auto &v : st.V) best = std::max(best, Dot(Rot(q.w, v), d));
    s += l[k] * (best - h);
  }
  return s / sl;
}

std::vector<int> Hull2(const std::vector<std::array<double, 2>> &P, double tol) {
  const int n = P.size();
  std::vector<int> idx(n);
  for (int i = 0; i < n; i++) idx[i] = i;
  std::sort(idx.begin(), idx.end(), [&](int a, int b) { return P[a] < P[b]; });
  auto cr = [&](int o, int a, int b) {
    return (P[a][0] - P[o][0]) * (P[b][1] - P[o][1]) - (P[a][1] - P[o][1]) * (P[b][0] - P[o][0]);
  };
  std::vector<int> H;
  for (int pass = 0; pass < 2; pass++) {
    const size_t start = H.size();
    for (int i : idx) {
      while (H.size() >= start + 2 && cr(H[H.size() - 2], H.back(), i) <= tol) H.pop_back();
      H.push_back(i);
    }
    H.pop_back();
    std::reverse(idx.begin(), idx.end());
  }
  return H;
}

// The contact pool at a pose: the shadow's hull edges, oriented so that
// d = u x c is the outward normal.
std::vector<Contact> ContactPool(const Setup &st, const Pose &q) {
  std::vector<Contact> pool;
  const V3<double> u = Scale(1 / Norm(q.u), q.u);
  V3<double> f = Cross({0, 0, 1}, u);
  if (Norm(f) < 1e-6) f = Cross({1, 0, 0}, u);
  f = Scale(1 / Norm(f), f);
  const V3<double> g = Cross(u, f);
  const int n = st.V.size();
  std::vector<std::array<double, 2>> P(n);
  for (int i = 0; i < n; i++) P[i] = {Dot(st.V[i], f), Dot(st.V[i], g)};
  const std::vector<int> H = Hull2(P, 1e-14);
  for (size_t k = 0; k < H.size(); k++) {
    const int a = H[k], b = H[(k + 1) % H.size()];
    const double dx = P[b][0] - P[a][0], dy = P[b][1] - P[a][1], l = std::hypot(dx, dy);
    if (l < 1e-14) continue;
    const V3<double> nrm = Add(Scale(dy / l, f), Scale(-dx / l, g));
    Contact c;
    c.a = a;
    c.b = b;
    c.c = Sub(st.V[b], st.V[a]);
    if (Dot(Cross(q.u, c.c), nrm) < 0) { std::swap(c.a, c.b); c.c = Scale(-1, c.c); }
    const V3<double> d = Cross(q.u, c.c);
    c.S = SupportSet(st, d);
    double best = -1e300;
    for (int i : c.S) {
      const double v = Dot(Rot(q.w, st.V[i]), d);
      if (v > best) { best = v; c.i = i; }
    }
    pool.push_back(c);
  }
  return pool;
}

std::vector<Witness> Combine(const Setup &st, const std::vector<Contact> &pool, const Pose &q, int keep) {
  std::vector<std::pair<double, Witness>> out;
  const int m = pool.size();
  for (int a = 0; a < m; a++) {
    // A width: a with its exact opposite (the reversed edge).
    Contact o = pool[a];
    std::swap(o.a, o.b);
    o.c = Scale(-1, pool[a].c);
    const V3<double> dd = Cross(q.u, o.c);
    o.S = SupportSet(st, dd);
    double best = -1e300;
    for (int i : o.S) {
      const double v = Dot(Rot(q.w, st.V[i]), dd);
      if (v > best) { best = v; o.i = i; }
    }
    Witness W{{pool[a], o}, 1};
    out.push_back({Value(st, W, q), W});
    for (int b = a + 1; b < m; b++)
      for (int c = b + 1; c < m; c++) {
        Witness T{{pool[a], pool[b], pool[c]}, 1};
        std::vector<double> l = Weights(T, q);
        if (l[0] < 0 && l[1] < 0 && l[2] < 0) { T.s = -1; for (double &x : l) x = -x; }
        if (!(l[0] > 0 && l[1] > 0 && l[2] > 0)) continue;
        out.push_back({Value(st, T, q), T});
      }
  }
  std::sort(out.begin(), out.end(), [](const auto &x, const auto &y) { return x.first > y.first; });
  std::vector<Witness> r;
  for (int i = 0; i < (int)out.size() && (int)r.size() < keep; i++) if (out[i].first > 0) r.push_back(out[i].second);
  return r;
}

// ----- Leaves -----
struct Leaf {
  int K = 0, s = 1;
  std::vector<std::pair<int, int>> edges;
  std::vector<std::vector<int>> S;
  std::vector<std::vector<int>> inner;  // per tuple, K inner indices
  // Blended inner points (Lean KCap.Leaf.blends): inner index V.size() + b
  // is the point (1 - t) v_a + t v_b of blends[b] = (a, b, t = tn / 4).
  struct Blend { int a = 0, b = 0, tn = 0; };
  std::vector<Blend> blends;
};

// A leaf's pack tokens (Lean PackedLocalViewTree.readKLeaf).
std::string LeafTokens(const Leaf &l) {
  std::string r = std::to_string(l.K) + "," + ZigzagRat(Q(l.s));
  for (int k = 0; k < l.K; k++) {
    r += "," + std::to_string(l.edges[k].first) + "," + std::to_string(l.edges[k].second) + "," +
         std::to_string(l.S[k].size());
    for (int j : l.S[k]) r += "," + std::to_string(j);
  }
  r += "," + std::to_string(l.inner.size());
  for (const auto &it : l.inner)
    for (int i : it) r += "," + std::to_string(i);
  return r;
}

// A leaf with its tag (Lean PackedLocalViewTree.readATree): 1, or 4 with
// the blends first (count, then per blend a, b, t).
std::string LeafTokensTagged(const Leaf &l) {
  if (l.blends.empty()) return "1," + LeafTokens(l);
  std::string r = "4," + std::to_string(l.blends.size());
  for (const Leaf::Blend &b : l.blends)
    r += "," + std::to_string(b.a) + "," + std::to_string(b.b) + "," + ZigzagRat(Q(b.tn, 4));
  return r + "," + LeafTokens(l);
}

struct Stats {
  std::atomic<int64_t> ok{0}, failed{0}, visited{0}, exact_fail{0}, affine{0}, blended{0};
  std::atomic<int> max_depth{0};
  // Nodes allowed per chart (0: unlimited); past it the chart fails.
  int64_t budget = 0;
};

std::atomic<int> g_active{0};
int g_max_active = 128;

struct Certifier {
  const Setup &st;
  ChartId id;
  Box chart_box;
  int max_depth;
  Stats *stats;
  Chart<double> ch;
  std::mutex mu;
  std::vector<std::string> fail_boxes;

  Chart<Q> chq;
  // This certifier's coordinates: y = map(z), over boxes in z; affine nodes
  // start a child certifier with the new map.
  AffMapQ map;
  int depth0 = 0;  // the depth of this certifier's root (an affine node)

  Certifier(const Setup &s, const ChartId &i, int md, Stats *stt, const AffMapQ &m = AffMapQ::Identity(),
            const Box *root = nullptr, int d0 = 0)
      : st(s), id(i), chart_box(root ? *root : ChartBox(s)), max_depth(md), stats(stt),
        ch(MakeChart<double>(s, i, m)), map(m), depth0(d0) {
    if (g_exact) chq = MakeChart<Q>(s, i, m);
  }

  template <class T> PolyT<T> Reduce(PolyT<T> P) const { return DivideVar(P, 0); }

  template <class T> struct Parts {
    std::vector<PV<T>> d, L;  // d_k, lambda_k d_k
    std::vector<PolyT<T>> lam;
  };
  template <class T> Parts<T> MakeParts(const Chart<T> &c, const std::vector<V3<T>> &dirs, int s) const {
    Parts<T> p;
    const int K = dirs.size();
    for (int k = 0; k < K; k++) p.d.push_back(PCross(c.u, PConst(dirs[k])));
    if (K == 2) {
      p.lam = {PolyT<T>::Const(One<T>()), PolyT<T>::Const(One<T>())};
    } else {
      for (int k = 0; k < 3; k++) {
        const V3<T> cc = VCross(dirs[(k + 1) % 3], dirs[(k + 2) % 3]);
        p.lam.push_back(FromQ<T>(Q(s)) * PDot(c.u, cc));
      }
    }
    for (int k = 0; k < K; k++) p.L.push_back(p.lam[k] * p.d[k]);
    return p;
  }

  // The double screen of witness W on the box: the minimum over the tuples of
  // the best inner choice's Bernstein bound of P / mu (-inf when a weight,
  // strictness or the tuple count fails). Inner choices: per contact the
  // vertices of its outer set (where they tie with the outer choice at
  // mu = 0, the mu^0 term vanishes). Fills the leaf when given and the
  // score is >= -1e-13; `why` gets the failing part.
  double Score(const Witness &W, const Box &box, Leaf *leaf = nullptr, std::string *why = nullptr,
               PolyT<double> *worst_poly = nullptr) {
    const bool blend = g_blend;
    const double kFail = -1e300;
    const int K = W.k.size();
    std::vector<V3<double>> dirs;
    for (const Contact &c : W.k) dirs.push_back(c.c);
    const Parts<double> P = MakeParts(ch, dirs, W.s);
    if (K == 3)
      for (int k = 0; k < 3; k++)
        if (BernsteinLowerD(P.lam[k], box) < 0) {
          if (why) *why = "weight " + std::to_string(k);
          return kFail;
        }
    {
      PolyT<double> sl;
      for (int k = 0; k < K; k++) sl = sl + PDot(P.L[k], P.d[k]);
      if (!(BernsteinLowerD(sl, box) > 0)) {
        if (why) *why = "strictness";
        return kFail;
      }
    }
    // Dominance: vertices not dominated by S_k[0] join S_k.
    std::vector<std::vector<int>> S(K);
    for (int k = 0; k < K; k++) {
      S[k] = W.k[k].S;
      for (int j = 0; j < (int)st.V.size(); j++) {
        if (std::find(W.k[k].S.begin(), W.k[k].S.end(), j) != W.k[k].S.end()) continue;
        const PolyT<double> dom = PDot(P.d[k], Sub(st.V[W.k[k].S[0]], st.V[j]));
        if (BernsteinLowerD(dom, box) < 0) S[k].push_back(j);
      }
    }
    // Inner candidates: the outer set (ties at mu = 0) and the two vertices
    // best along d_k after the rotation at the box's center (farther from
    // the identity another vertex can be the best inner choice).
    std::vector<std::vector<int>> I(K);
    {
      std::array<double, NV> c;
      for (int i = 0; i < NV; i++) c[i] = 0.5 * (box[i].first + box[i].second);
      const Pose q = PoseAt(ch, c.data());
      for (int k = 0; k < K; k++) {
        I[k] = S[k];
        const V3<double> d = Cross(q.u, W.k[k].c);
        std::vector<std::pair<double, int>> by;
        for (int v = 0; v < (int)st.V.size(); v++) by.push_back({Dot(Rot(q.w, st.V[v]), d), v});
        std::sort(by.rbegin(), by.rend());
        for (int r = 0; r < 2 && r < (int)by.size(); r++)
          if (std::find(I[k].begin(), I[k].end(), by[r].second) == I[k].end()) I[k].push_back(by[r].second);
      }
    }
    int64_t ntup = 1, ninner = 1;
    for (int k = 0; k < K; k++) {
      // (An empty outer set: a degenerate pose, e.g. non-finite.)
      if (S[k].empty()) {
        if (why) *why = "empty outer set";
        return kFail;
      }
      ntup *= S[k].size();
      ninner *= I[k].size();
    }
    if (ntup > 512) {
      if (why) *why = "tuples";
      return kFail;
    }
    std::vector<std::map<int, PolyT<double>>> A(K), B(K);
    auto Aof = [&](int k, int i) -> const PolyT<double> & {
      auto it = A[k].find(i);
      if (it != A[k].end()) return it->second;
      return A[k][i] = PDot(ch.NV_[i], P.L[k]);
    };
    auto Bof = [&](int k, int j) -> const PolyT<double> & {
      auto it = B[k].find(j);
      if (it != B[k].end()) return it->second;
      return B[k][j] = ch.D * PDot(P.L[k], st.V[j]);
    };
    if (leaf) { leaf->inner.clear(); leaf->blends.clear(); }
    double score = 1e300;
    for (int64_t tix = 0; tix < ntup; tix++) {
      int64_t r = tix;
      std::vector<int> jt(K);
      for (int k = 0; k < K; k++) { jt[k] = S[k][r % S[k].size()]; r /= S[k].size(); }
      double best = kFail;
      std::vector<int> best_it;
      struct Cand { double bnd; PolyT<double> P; std::vector<int> it; };
      std::vector<Cand> polys;
      // The winning blend, per contact: vertices a, b at t = tn / 4 (tn = 0:
      // the vertex a); empty: none.
      std::vector<Leaf::Blend> bchoice;
      for (int64_t ci = 0; ci < ninner; ci++) {
        int64_t q = ci;
        std::vector<int> it(K);
        for (int k = 0; k < K; k++) { it[k] = I[k][q % I[k].size()]; q /= I[k].size(); }
        PolyT<double> Pp;
        for (int k = 0; k < K; k++) Pp = Pp + (Aof(k, it[k]) - Bof(k, jt[k]));
        const double bnd = BernsteinLowerD(Reduce(Pp), box);
        if (bnd > best) { best = bnd; best_it = it; }
        if (blend) polys.push_back({bnd, std::move(Pp), it});
      }
      // (Experiment, --blend: inner points on the segment between two inner
      // choices' vertices, p_k = (1 - t) v_{a_k} + t v_{b_k}; sound because
      // R p . d <= max(R v_a . d, R v_b . d). Double screen only so far.)
      if (blend && best < 0 && polys.size() > 1) {
        std::sort(polys.begin(), polys.end(), [](auto &a, auto &b) { return a.bnd > b.bnd; });
        const int m = std::min<int>(6, polys.size());
        for (int a = 0; a < m; a++)
          for (int b = a + 1; b < m; b++)
            for (int tn : {1, 2, 3}) {
              const double t = tn / 4.0;
              const PolyT<double> Bl = (1 - t) * polys[a].P + t * polys[b].P;
              const double bnd = BernsteinLowerD(Reduce(Bl), box);
              if (bnd > best) {
                best = bnd;
                bchoice.resize(K);
                for (int k = 0; k < K; k++)
                  bchoice[k] = {polys[a].it[k], polys[b].it[k], polys[a].it[k] == polys[b].it[k] ? 0 : tn};
              }
            }
        // --blend_contacts: each contact its own blend (P is a sum over the
        // contacts, so p_k may differ per k): coordinate ascent from the
        // best so far, two rounds over the contacts.
        if ((g_blend_contacts >= 2 || (g_blend_contacts == 1 && leaf != nullptr)) && best < 0) {
          if (bchoice.empty()) {
            bchoice.resize(K);
            for (int k = 0; k < K; k++) bchoice[k] = {best_it[k], best_it[k], 0};
          }
          auto Term = [&](int k, const Leaf::Blend &c) -> PolyT<double> {
            if (c.tn == 0) return Aof(k, c.a);
            const double t = c.tn / 4.0;
            return (1 - t) * Aof(k, c.a) + t * Aof(k, c.b);
          };
          for (int round = 0; round < 2 && best < 0; round++)
            for (int k = 0; k < K && best < 0; k++) {
              PolyT<double> rest;
              for (int k2 = 0; k2 < K; k2++)
                rest = rest + ((k2 == k ? PolyT<double>() : Term(k2, bchoice[k2])) - Bof(k2, jt[k2]));
              for (int ia = 0; ia < (int)I[k].size(); ia++)
                for (int ib = ia; ib < (int)I[k].size(); ib++)
                  for (int tn : {0, 1, 2, 3}) {
                    if ((ia == ib) != (tn == 0)) continue;
                    const Leaf::Blend c{I[k][ia], I[k][ib], tn};
                    const double bnd = BernsteinLowerD(Reduce(rest + Term(k, c)), box);
                    if (bnd > best) { best = bnd; bchoice[k] = c; }
                  }
            }
        }
        bool any = false;
        for (const Leaf::Blend &c : bchoice) any = any || c.tn > 0;
        if (any) stats->blended++; else bchoice.clear();
      }
      if (worst_poly != nullptr && best < score) {
        PolyT<double> Pp;
        for (int k = 0; k < K; k++) Pp = Pp + (Aof(k, best_it[k]) - Bof(k, jt[k]));
        *worst_poly = Reduce(Pp);
      }
      score = std::min(score, best);
      if (best < -1e-13) {
        if (why) {
          *why = "tuple (outer";
          for (int j : jt) *why += " " + std::to_string(j);
          *why += ") best bound " + std::to_string(best);
          // The best inner choice's polynomial on a 7^5 grid of the box:
          // negative means no box splitting helps this inner choice.
          PolyT<double> Pp;
          for (int k = 0; k < K; k++) Pp = Pp + (Aof(k, best_it[k]) - Bof(k, jt[k]));
          const PolyT<double> R = Reduce(Pp);
          double gmin = 1e300;
          for (int g = 0; g < 16807; g++) {
            double y[NV];
            int r = g;
            for (int i = 0; i < NV; i++) {
              y[i] = box[i].first + (r % 7) / 6.0 * (box[i].second - box[i].first);
              r /= 7;
            }
            gmin = std::min(gmin, Eval(R, y));
          }
          *why += ", its grid min " + std::to_string(gmin) + " (inner";
          for (int i : best_it) *why += " " + std::to_string(i);
          *why += ")";
          // Every inner choice: its bound and grid min.
          for (int64_t ci = 0; ci < ninner; ci++) {
            int64_t q = ci;
            std::vector<int> it(K);
            for (int k = 0; k < K; k++) { it[k] = I[k][q % I[k].size()]; q /= I[k].size(); }
            PolyT<double> P2;
            for (int k = 0; k < K; k++) P2 = P2 + (Aof(k, it[k]) - Bof(k, jt[k]));
            const PolyT<double> R2 = Reduce(P2);
            double gm = 1e300;
            for (int g = 0; g < 16807; g++) {
              double y[NV];
              int r = g;
              for (int i = 0; i < NV; i++) {
                y[i] = box[i].first + (r % 7) / 6.0 * (box[i].second - box[i].first);
                r /= 7;
              }
              gm = std::min(gm, Eval(R2, y));
            }
            *why += "\n        inner";
            for (int i : it) *why += " " + std::to_string(i);
            *why += ": bound " + std::to_string(BernsteinLowerD(R2, box)) + " grid min " + std::to_string(gm);
          }
        }
        if (!leaf) continue;
        return score;
      }
      if (leaf && !bchoice.empty()) {
        std::vector<int> it(K);
        for (int k = 0; k < K; k++) {
          if (bchoice[k].tn == 0) { it[k] = bchoice[k].a; continue; }
          const Leaf::Blend bl = bchoice[k];
          int bi = 0;
          while (bi < (int)leaf->blends.size() && !(leaf->blends[bi].a == bl.a && leaf->blends[bi].b == bl.b &&
                                                     leaf->blends[bi].tn == bl.tn))
            bi++;
          if (bi == (int)leaf->blends.size()) leaf->blends.push_back(bl);
          it[k] = (int)st.V.size() + bi;
        }
        leaf->inner.push_back(it);
      } else if (leaf) {
        leaf->inner.push_back(best_it);
      }
    }
    if (leaf) {
      leaf->K = K;
      leaf->s = W.s;
      leaf->edges.clear();
      for (const Contact &c : W.k) leaf->edges.push_back({c.a, c.b});
      leaf->S = S;
    }
    return score;
  }

  bool Check(const Witness &W, const Box &box, Leaf *leaf, std::string *why = nullptr) {
    return Score(W, box, leaf, why) >= -1e-13;
  }

  // The exact check of a screened leaf: Lean's KCap.Leaf.check (idChartId:
  // the tuple polynomials divided by mu).
  bool Exact(const Leaf &leaf, const Box &box) {
    const auto bq = BoxQ(box);
    const int K = leaf.K;
    std::vector<V3<Q>> dirs;
    for (const auto &[a, b] : leaf.edges) dirs.push_back(VSub(st.VQ[b], st.VQ[a]));
    const Parts<Q> P = MakeParts(chq, dirs, leaf.s);
    if (g_affine) {
      // (Debugging the affine mode: every operand must be a valid rational.)
      auto Valid = [&](const PolyT<Q> &poly, const std::string &what) {
        for (const auto &[e, q] : poly.t)
          CHECK(!(q.Denominator() == BigInt(0))) << "zero denominator in " << what << " (map ident "
                                                  << map.ident << ")";
      };
      for (size_t i = 0; i < chq.NV_.size(); i++)
        for (int a = 0; a < 3; a++) Valid(chq.NV_[i][a], "NV_" + std::to_string(i));
      Valid(chq.D, "D");
      for (int k = 0; k < K; k++) {
        Valid(P.lam[k], "lam" + std::to_string(k));
        for (int a = 0; a < 3; a++) { Valid(P.d[k][a], "d"); Valid(P.L[k][a], "L"); }
      }
    }
    if (K == 3)
      for (int k = 0; k < 3; k++) if (!ExactLowerOk(P.lam[k], bq, false)) return false;
    {
      PolyT<Q> sl;
      for (int k = 0; k < K; k++) sl = sl + PDot(P.L[k], P.d[k]);
      if (!ExactLowerOk(sl, bq, true)) return false;
    }
    for (int k = 0; k < K; k++) {
      const auto &S = leaf.S[k];
      for (int j = 0; j < (int)st.VQ.size(); j++) {
        if (std::find(S.begin(), S.end(), j) != S.end()) continue;
        if (!ExactLowerOk(PDot(P.d[k], VSub(st.VQ[S[0]], st.VQ[j])), bq, false)) return false;
      }
    }
    std::vector<std::map<int, PolyT<Q>>> A(K), B(K);
    const int nv = st.VQ.size();
    std::function<const PolyT<Q> &(int, int)> Aof = [&](int k, int i) -> const PolyT<Q> & {
      auto it = A[k].find(i);
      if (it != A[k].end()) return it->second;
      if (i >= nv) {
        // A blended inner point (Lean Leaf.innerNum): (1 - t) N v_a + t N v_b.
        const Leaf::Blend &bl = leaf.blends[i - nv];
        const Q t(bl.tn, 4);
        PolyT<Q> r = (Q(1) - t) * Aof(k, bl.a) + t * Aof(k, bl.b);
        return A[k][i] = std::move(r);
      }
      return A[k][i] = PDot(chq.NV_[i], P.L[k]);
    };
    auto Bof = [&](int k, int j) -> const PolyT<Q> & {
      auto it = B[k].find(j);
      if (it != B[k].end()) return it->second;
      return B[k][j] = chq.D * PDot(P.L[k], st.VQ[j]);
    };
    int64_t ntup = 1;
    for (int k = 0; k < K; k++) ntup *= leaf.S[k].size();
    CHECK((int64_t)leaf.inner.size() == ntup);
    for (int64_t tix = 0; tix < ntup; tix++) {
      int64_t r = tix;
      PolyT<Q> Pp;
      for (int k = 0; k < K; k++) {
        const int j = leaf.S[k][r % leaf.S[k].size()];
        r /= leaf.S[k].size();
        Pp = Pp + (Aof(k, leaf.inner[tix][k]) - Bof(k, j));
      }
      if (!ExactLowerOk(DivideVar(Pp, 0), bq, false)) return false;
    }
    return true;
  }

  // Returns the number of leaves of the subtree (0: failed).
  int64_t last_affine_leaves_ = 0;

  // An affine node at box (center c): in box-scaled coordinates of variables
  // i1, i2, a rotation taking the first new axis along (g1, g2); the map to
  // the original variables is this certifier's composed with it, rounded to
  // short dyadics and inverted exactly; the child box is the exact interval
  // image of this box, rounded outward (so it covers by construction).
  // Returns the subtree's tokens.
  std::optional<std::string> AffineNode(const Box &box, int depth, const std::array<double, NV> &c, int i1,
                                        int i2, double g1, double g2, bool *ok) {
    const double w1 = box[i1].second - box[i1].first, w2 = box[i2].second - box[i2].first;
    if (!(w1 > 0 && w2 > 0) || !std::isfinite(g1) || !std::isfinite(g2)) return std::nullopt;
    const double th = std::atan2(g2, g1);
    // z_old = c + Arel (z_new - c), Arel = D R D^-1 in the (i1, i2) plane.
    double R[2][2] = {{std::cos(th), -std::sin(th)}, {std::sin(th), std::cos(th)}};
    double Arel[NV][NV];
    for (int i = 0; i < NV; i++) for (int j = 0; j < NV; j++) Arel[i][j] = i == j ? 1 : 0;
    const int ix[2] = {i1, i2};
    const double w[2] = {w1, w2};
    for (int a = 0; a < 2; a++)
      for (int b = 0; b < 2; b++) Arel[ix[a]][ix[b]] = w[a] * R[a][b] / w[b];
    // The new absolute map: A' = A Arel, c' = A (c - Arel c) + cA, rounded.
    AffMapQ m;
    m.ident = false;
    double cz[NV];
    for (int i = 0; i < NV; i++) {
      cz[i] = c[i];
      for (int j = 0; j < NV; j++) cz[i] -= Arel[i][j] * c[j];
    }
    for (int i = 0; i < NV; i++) {
      double ci = map.c[i].ToDouble();
      for (int k = 0; k < NV; k++) ci += map.A[i][k].ToDouble() * cz[k];
      m.c[i] = i == 0 ? Q(0) : DyadicRat(RoundDyadic(ci, 24));
      for (int j = 0; j < NV; j++) {
        double a = 0;
        for (int k = 0; k < NV; k++) a += map.A[i][k].ToDouble() * Arel[k][j];
        m.A[i][j] = (i == 0 || j == 0) ? Q(i == j ? 1 : 0) : DyadicRat(RoundDyadic(a, 16));
      }
    }
    if (!Invert(m.A, &m.B)) return std::nullopt;
    // (Every rational of the map must be a valid one: a zero denominator
    // would be a bug here, and GMP reports it only later, as SIGFPE.)
    auto ValidQ = [&](const Q &q, const char *what, int i, int j) {
      CHECK(!(q.Denominator() == BigInt(0))) << "zero denominator in " << what << "[" << i << "][" << j
                                              << "] at depth " << depth;
    };
    for (int i = 0; i < NV; i++) {
      ValidQ(m.c[i], "c", i, 0);
      for (int j = 0; j < NV; j++) { ValidQ(m.A[i][j], "A", i, j); ValidQ(m.B[i][j], "B", i, j); }
    }
    // The child box: the image of this box under z -> B'(A z + cA - c'), exactly.
    const auto bq = BoxQ(box);
    Box child;
    for (int i = 0; i < NV; i++) {
      Q lo(0), hi(0);
      for (int k = 0; k < NV; k++) {
        const Q d = map.c[k] - m.c[k];
        lo = lo + m.B[i][k] * d;
      }
      hi = lo;
      for (int j = 0; j < NV; j++) {
        Q M(0);
        for (int k = 0; k < NV; k++) M = M + m.B[i][k] * map.A[k][j];
        if (M == Q(0)) continue;
        const Q a = M * bq[j].first, b = M * bq[j].second;
        if (Q::Sign(M) > 0) { lo = lo + a; hi = hi + b; } else { lo = lo + b; hi = hi + a; }
      }
      // Outward to 2^-30 (doubles exactly).
      child[i] = {FloorDyadic(lo.ToDouble(), 30) - std::ldexp(1, -30), CeilDyadic(hi.ToDouble(), 30) + std::ldexp(1, -30)};
      if (i == 0) child[i].first = std::max(0.0, std::min(child[i].first, box[0].first));
      if (!std::isfinite(child[i].first) || !std::isfinite(child[i].second)) return std::nullopt;
    }
    // A well-conditioned map: the child box (in the rotated variables, in
    // units of the parent's widths) at most 3 times the parent's area (a
    // rotated box's bounding box is at most twice it).
    {
      double ratio = 1;
      for (int a = 0; a < 2; a++) {
        const int i = ix[a];
        ratio *= (child[i].second - child[i].first) / w[a];
      }
      // (The rotated variables keep their scale: the new axes are in units of
      // the old widths.)
      if (!(ratio > 0 && ratio <= 3)) return std::nullopt;
    }
    stats->affine++;
    for (int i = 0; i < NV; i++) {
      ValidQ(DyadicRat(child[i].first), "child lo", i, 0);
      ValidQ(DyadicRat(child[i].second - child[i].first), "child width", i, 0);
    }
    Certifier sub(st, id, max_depth, stats, m, &child, depth + 1);
    if (g_exact) {
      for (const auto &pv : {sub.chq.u, sub.chq.w})
        for (const auto &poly : pv)
          for (const auto &[e, q] : poly.t) ValidQ(q, "chart coefficient", e[0], e[1]);
    }
    std::string t;
    last_affine_leaves_ = sub.Rec(child, depth + 1, ok, &t);
    {
      std::lock_guard<std::mutex> l(mu);
      for (const auto &f : sub.fail_boxes) if (fail_boxes.size() < 6u) fail_boxes.push_back(f);
    }
    std::string r = "3";
    for (int i = 0; i < NV; i++) for (int j = 0; j < NV; j++) r += "," + ZigzagRat(m.A[i][j]);
    for (int i = 0; i < NV; i++) r += "," + ZigzagRat(m.c[i]);
    for (int i = 0; i < NV; i++) for (int j = 0; j < NV; j++) r += "," + ZigzagRat(m.B[i][j]);
    for (int i = 0; i < NV; i++) r += "," + ZigzagRat(DyadicRat(child[i].first));
    for (int i = 0; i < NV; i++) r += "," + ZigzagRat(DyadicRat(child[i].second - child[i].first));
    return r + "," + t;
  }

  // Certifies the box; *tokens gets its subtree in preorder (Lean
  // PackedLocalViewTree.readKTree: 0 axis left right, 1 leaf, 2 failed).
  // Returns the number of leaves.
  int64_t Rec(Box box, int depth, bool *ok, std::string *tokens) {
    if (stats->budget > 0 && stats->visited.fetch_add(1) >= stats->budget) {
      *ok = false;
      *tokens = "2";
      return 0;
    }
    {
      int m = stats->max_depth.load();
      while (depth > m && !stats->max_depth.compare_exchange_weak(m, depth)) {}
    }
    std::array<double, NV> c;
    for (int i = 0; i < NV; i++) c[i] = 0.5 * (box[i].first + box[i].second);
    std::vector<std::array<double, NV>> pts{c};
    for (int i = 0; i < NV; i++) {
      auto lo = c, hi = c;
      lo[i] = box[i].first;
      hi[i] = box[i].second;
      pts.push_back(lo);
      pts.push_back(hi);
    }
    // (At mu = 0 every witness has value 0: sample just above it, and rank
    // by value / mu, so that a witness whose first-order term is negative
    // somewhere is not preferred for its value farther out.)
    for (auto &x : pts) if (x[0] == 0) x[0] = 1e-3 * box[0].second;

    std::vector<Witness> cands;
    for (int pi : {0, 3, 5, 7, 9}) {
      const Pose q = PoseAt(ch, pts[pi].data());
      for (Witness &w : Combine(st, ContactPool(st, q), q, pi == 0 ? 24 : 8)) cands.push_back(std::move(w));
    }
    std::vector<std::pair<double, int>> sc;
    for (int wi = 0; wi < (int)cands.size(); wi++) {
      double worst = 1e300;
      for (const auto &x : pts) worst = std::min(worst, Value(st, cands[wi], PoseAt(ch, x.data())) / x[0]);
      sc.push_back({worst, wi});
    }
    std::sort(sc.begin(), sc.end(), [](auto &a, auto &b) { return a.first > b.first; });
    const int ntry = std::min<int>(g_try, sc.size());
    for (int r = 0; r < ntry; r++) {
      if (sc[r].first <= 0) break;
      Leaf leaf;
      if (!Check(cands[sc[r].second], box, &leaf)) continue;
      if (g_exact && !Exact(leaf, box)) {
        stats->exact_fail++;
        continue;
      }
      stats->ok++;
      *ok = true;
      *tokens = LeafTokensTagged(leaf);
      return 1;
    }
    if (depth >= max_depth) {
      stats->failed++;
      std::lock_guard<std::mutex> l(mu);
      if (fail_boxes.size() < 6u) {
        std::string s;
        for (auto &[lo, hi] : box) s += std::to_string(lo) + ".." + std::to_string(hi) + " ";
        s += " best " + (sc.empty() ? std::string("none") : std::to_string(sc[0].first));
        if (!sc.empty()) {
          const Witness &W = cands[sc[0].second];
          Leaf l2;
          std::string why;
          Check(W, box, &l2, &why);
          // The witness's minimum on a 5^5 grid of the box (mu > 0).
          double gmin = 1e300;
          for (int g = 0; g < 3125; g++) {
            std::array<double, NV> y;
            int r = g;
            for (int i = 0; i < NV; i++) {
              const double f = (r % 5) / 4.0;
              r /= 5;
              y[i] = box[i].first + f * (box[i].second - box[i].first);
            }
            if (y[0] == 0) y[0] = 1e-6 * box[0].second;
            gmin = std::min(gmin, Value(st, W, PoseAt(ch, y.data())) / y[0]);
          }
          s += "\n      K=" + std::to_string(W.k.size()) + " edges";
          for (const Contact &c : W.k) s += " " + std::to_string(c.a) + "-" + std::to_string(c.b);
          s += ": " + why + "; grid min of value/mu " + std::to_string(gmin);
        }
        fail_boxes.push_back(s);
      }
      *ok = false;
      *tokens = "2";
      return 0;
    }
    // An affine node: where the best candidate's worst tuple fails and its
    // polynomial's gradient (in the box-scaled view and direction
    // variables) is far from every axis, rotate the plane of its two largest
    // components so that one new axis follows it.
    // (At most one affine node per path: a rotated box's bounding box is
    // larger, so repeated rotations can outgrow the splits.)
    if (g_affine && map.ident && !sc.empty() && depth - depth0 >= g_affine_gap) {
      PolyT<double> wp;
      const double sco = Score(cands[sc[0].second], box, nullptr, nullptr, &wp);
      if (sco < 0 && !wp.t.empty()) {
        double g[NV] = {0, 0, 0, 0, 0};
        for (int i = 1; i < NV; i++) {
          const double h = 0.25 * (box[i].second - box[i].first);
          std::array<double, NV> a = c, b = c;
          a[i] -= h;
          b[i] += h;
          g[i] = (Eval(wp, b.data()) - Eval(wp, a.data())) * 2;  // per box width
        }
        int i1 = 1, i2 = 2;
        for (int i = 1; i < NV; i++) if (std::abs(g[i]) > std::abs(g[i1])) i1 = i;
        i2 = i1 == 1 ? 2 : 1;
        for (int i = 1; i < NV; i++) if (i != i1 && std::abs(g[i]) > std::abs(g[i2])) i2 = i;
        const double gn = std::hypot(g[i1], g[i2]);
        if (gn > 0 && std::abs(g[i1]) < 0.9 * gn) {
          if (auto t = AffineNode(box, depth, c, i1, i2, g[i1], g[i2], ok)) {
            *tokens = *t;
            return last_affine_leaves_;
          }
        }
      }
    }
    // Split the variable whose halves have the best worse-half score for the
    // best few candidates (the score: Score above, the quantity the leaf
    // check needs); without candidates, the widest variable relative to the
    // chart's box.
    int best = -1;
    double bw = -1e301;
    const double cur = sc.empty() ? -1e300 : Score(cands[sc[0].second], box);
    // --mu_guard: when every candidate fails on the box's lowest mu (the
    // face mu = lo; at lo = 0 the first-order term), no mu split can help:
    // split the other variables. (Otherwise each mu split may improve the
    // score a little, toward a negative limit, down to max_depth.)
    bool mu_futile = false;
    if (g_mu_guard && !sc.empty()) {
      auto h0 = box;
      h0[0].second = h0[0].first;
      mu_futile = true;
      for (int r = 0; r < std::min<int>(3, sc.size()) && mu_futile; r++)
        if (Score(cands[sc[r].second], h0) >= -1e-13) mu_futile = false;
    }
    for (int r = 0; r < std::min<int>(3, sc.size()); r++) {
      const Witness &W = cands[sc[r].second];
      for (int i = mu_futile ? 1 : 0; i < NV; i++) {
        const double mid = 0.5 * (box[i].first + box[i].second);
        auto h1 = box, h2 = box;
        h1[i].second = mid;
        h2[i].first = mid;
        const double v = std::min(Score(W, h1), Score(W, h2));
        if (v > bw) { bw = v; best = i; }
      }
    }
    // A lookahead that does not improve the score (by 10% of its deficit)
    // is myopic (an inner choice switching along a slanted line needs
    // several splits of the direction): then the widest variable relative
    // to the chart's box, the direction (p1, p2) weighted 4 times mu and the
    // view.
    if (best < 0 || bw <= -1e299 || (cur < 0 && bw < cur + 0.1 * -cur)) {
      best = mu_futile ? 1 : 0;
      bw = -1;
      for (int i = mu_futile ? 1 : 0; i < NV; i++) {
        const double rel = (box[i].second - box[i].first) / (chart_box[i].second - chart_box[i].first) * (i >= 3 ? 4 : 1);
        if (rel > bw) { bw = rel; best = i; }
      }
    }
    const double m = 0.5 * (box[best].first + box[best].second);
    auto b1 = box, b2 = box;
    b1[best].second = m;
    b2[best].first = m;
    bool ok1 = false, ok2 = false;
    int64_t n1 = 0, n2 = 0;
    std::string t1, t2;
    if (g_active.load() < g_max_active) {
      g_active++;
      auto fut = std::async(std::launch::async, [&]() { return Rec(b2, depth + 1, &ok2, &t2); });
      n1 = Rec(b1, depth + 1, &ok1, &t1);
      n2 = fut.get();
      g_active--;
    } else {
      n1 = Rec(b1, depth + 1, &ok1, &t1);
      n2 = Rec(b2, depth + 1, &ok2, &t2);
    }
    *ok = ok1 && ok2;
    *tokens = "0," + std::to_string(best) + "," + t1 + "," + t2;
    return n1 + n2;
  }
};

// Certifies the six (or given) charts over st's triangle; false as soon as a
// chart fails. *leaves gets the total.
bool CertifyTriangle(const Setup &st, const std::vector<ChartId> &charts, int max_depth, int64_t budget,
                     int64_t *leaves, bool verbose, std::string *pack = nullptr) {
  *leaves = 0;
  // The row's tokens after rho: the vertex count, the faces, per face its
  // axis, sign (1: +) and tree.
  std::string out = std::to_string(st.VQ.size()) + "," + std::to_string(charts.size());
  for (const ChartId &id : charts) {
    Stats stats;
    stats.budget = budget;
    Certifier cert(st, id, max_depth, &stats);
    bool ok = false;
    const auto t1 = std::chrono::steady_clock::now();
    std::string tokens;
    const int64_t n = cert.Rec(ChartBox(st), 0, &ok, &tokens);
    out += "," + std::to_string(id.axis) + "," + (id.sign ? "1" : "0") + "," + tokens;
    if (verbose) {
      const double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count();
      printf("  face %-5s %s  leaves %lld  failed %lld  exact-rejected %lld  affine %lld  blended %lld  depth %d  (%.1f s)\n",
             id.Name().c_str(), ok ? "OK  " : "FAIL", (long long)n, (long long)stats.failed.load(),
             (long long)stats.exact_fail.load(), (long long)stats.affine.load(), (long long)stats.blended.load(),
             stats.max_depth.load(), sec);
      for (const std::string &f : cert.fail_boxes) printf("    failed box %s\n", f.c_str());
    }
    *leaves += n;
    if (!ok) return false;
  }
  if (pack != nullptr) *pack = out;
  return true;
}

struct TreeStats { int64_t view_leaves = 0, cert_leaves = 0, failed = 0; int max_depth = 0; };

// The view tree below triangle t (path digits so far).
void ViewTree(Setup st, const tubetree::TriangleQ &t, const std::string &path, int depth, int view_depth,
              const std::vector<ChartId> &charts, int max_depth, int64_t budget, TreeStats *ts) {
  for (int k = 0; k < 3; k++) st.c[k] = {t.corners[k].x, t.corners[k].y, t.corners[k].z};
  int64_t leaves = 0;
  const auto t0 = std::chrono::steady_clock::now();
  const bool ok = CertifyTriangle(st, charts, max_depth, budget, &leaves, false);
  const double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  if (ok) {
    ts->view_leaves++;
    ts->cert_leaves += leaves;
    ts->max_depth = std::max(ts->max_depth, depth);
    printf("  view %-12s OK    %7lld leaves (%.1f s)\n", path.empty() ? "(root)" : path.c_str(), (long long)leaves, sec);
    return;
  }
  if (depth >= view_depth) {
    ts->failed++;
    printf("  view %-12s FAIL  (%.1f s)\n", path.empty() ? "(root)" : path.c_str(), sec);
    return;
  }
  tubetree::TriangleQ ch4[4];
  t.Subdivide(ch4);
  for (int c = 0; c < 4; c++)
    ViewTree(st, ch4[c], path + (char)('0' + c), depth + 1, view_depth, charts, max_depth, budget, ts);
}

// The first-order margin of the candidate witnesses at the triangle's center:
// for every direction sigma on a grid of the six cube faces, the best value / mu
// at mu = 1e-7 over the witnesses from the contact pool there; prints the
// worst directions.
void Probe(const Setup &st, int n) {
  V3<double> u{0, 0, 0};
  for (int k = 0; k < 3; k++) u = Add(u, ToD(st.c[k]));
  u = Scale(1 / Norm(u), u);
  const double mu = 1e-7;
  Pose q0{u, {0, 0, mu}};
  const std::vector<Contact> pool = ContactPool(st, q0);
  printf("probe at (%.6f, %.6f, %.6f): %zu hull edges:", u[0], u[1], u[2], pool.size());
  for (const Contact &c : pool) printf(" %d-%d", c.a, c.b);
  printf("\n");
  std::vector<std::pair<double, V3<double>>> worst;
  for (int ax = 0; ax < 3; ax++)
    for (int sg : {-1, 1})
      for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
          V3<double> s{0, 0, 0};
          s[ax] = sg;
          int o = 0;
          for (int k = 0; k < 3; k++)
            if (k != ax) s[k] = (o++ == 0 ? -1 + 2.0 * i / (n - 1) : -1 + 2.0 * j / (n - 1));
          const Pose q{u, Scale(mu, s)};
          double best = -1e300;
          for (const Witness &W : Combine(st, ContactPool(st, q), q, 1000)) best = std::max(best, Value(st, W, q) / mu);
          worst.push_back({best, s});
        }
  std::sort(worst.begin(), worst.end(), [](auto &a, auto &b) { return a.first < b.first; });
  for (int k = 0; k < 5 && k < (int)worst.size(); k++)
    printf("  sigma (%+.3f, %+.3f, %+.3f): best first-order value %+.4e\n", worst[k].second[0], worst[k].second[1],
           worst[k].second[2], worst[k].first);
}

// The tree pass: replaces subtrees of a tube tree by blow-up leaves where
// they certify (down to pass_depth, under the leaf budget) and the existing
// subtree certifies a smaller radius than rho; elsewhere the tree is kept.
struct PassStats {
  int64_t tried = 0, replaced = 0, cert_leaves = 0, removed_leaves = 0;
  std::string log;  // (printed per code: codes may run concurrently)
};

int64_t CountLeaves(const tubetree::TreeNode &n) {
  if (n.children.empty()) return 1;
  int64_t c = 0;
  for (const auto &ch : n.children) c += CountLeaves(*ch);
  return c;
}

void Pass(Setup st, tubetree::TreeNode *node, const tubetree::TriangleQ &t, int pass_depth,
          const std::vector<ChartId> &charts, int max_depth, int64_t budget, PassStats *ps) {
  const int depth = node->depth();
  if (depth > pass_depth) return;
  const tubetree::EffectiveBounds eb = tubetree::ComputeEffectiveBounds(*node);
  if (!(eb.r_lower >= st.rho)) {
    for (int k = 0; k < 3; k++) st.c[k] = {t.corners[k].x, t.corners[k].y, t.corners[k].z};
    int64_t leaves = 0;
    std::string pack;
    ps->tried++;
    const auto t0 = std::chrono::steady_clock::now();
    if (CertifyTriangle(st, charts, max_depth, budget, &leaves, false, &pack)) {
      const int64_t removed = CountLeaves(*node);
      ps->log += StringPrintf("  node %-10s idcap: %6lld leaves replace %lld tube leaves (r_lower %.2e) (%.1f s)\n",
             node->path.empty() ? "(root)" : node->path.c_str(), (long long)leaves, (long long)removed,
             eb.r_lower.ToDouble(), std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
      node->children.clear();
      node->direct_cert.reset();
      node->decomposed_cert.reset();
      node->cap.reset();
      node->idcap = tubetree::IdCapLeaf{st.rho, pack};
      node->direct_bounds = tubetree::NodeBounds{};
      node->direct_bounds.direct_r_lower = st.rho;
      node->direct_bounds.direct_r_upper = st.rho;
      ps->replaced++;
      ps->cert_leaves += leaves;
      ps->removed_leaves += removed;
      return;
    }
  }
  if (node->children.size() != 4) return;
  tubetree::TriangleQ ch4[4];
  t.Subdivide(ch4);
  for (int c = 0; c < 4; c++) Pass(st, node->children[c].get(), ch4[c], pass_depth, charts, max_depth, budget, ps);
}

// On a crash, the stack (raw addresses and the executable's load address,
// for addr2line -e idcap.exe <address - base>).
void CrashHandler(int sig) {
  void *frames[64];
  const int n = backtrace(frames, 64);
  char buf[128];
  const int len = snprintf(buf, sizeof(buf), "\nsignal %d; stack:\n", sig);
  write(2, buf, len);
  backtrace_symbols_fd(frames, n, 2);
  FILE *maps = fopen("/proc/self/maps", "r");
  if (maps != nullptr) {
    char line[512];
    if (fgets(line, sizeof(line), maps)) write(2, line, strlen(line));
    fclose(maps);
  }
  signal(sig, SIG_DFL);
  raise(sig);
}

std::vector<double> ParseDoubles(const std::string &s) {
  std::vector<double> r;
  size_t p = 0;
  while (p < s.size()) {
    size_t q = s.find(',', p);
    if (q == std::string::npos) q = s.size();
    r.push_back(std::stod(s.substr(p, q - p)));
    p = q + 1;
  }
  return r;
}

}  // namespace

int main(int argc, char **argv) {
  setvbuf(stdout, nullptr, _IOLBF, 0);
  signal(SIGFPE, CrashHandler);
  signal(SIGSEGV, CrashHandler);
  std::vector<double> view;
  double size = 1e-3;
  int code = -1, tri = 0, view_depth = -1, probe = 0, pass_depth = 6;
  std::string trees_in, trees_out, codes_arg;
  int64_t max_leaves = 0;
  int code_jobs = 1;
  std::string path, bdd = "codebdd.json";
  Q rho(1, 64);
  int max_depth = 40;
  std::vector<ChartId> charts;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a;
      return argv[++i];
    };
    if (a == "--view") view = ParseDoubles(next());
    else if (a == "--size") size = std::stod(next());
    else if (a == "--code") code = std::stoi(next());
    else if (a == "--tri") tri = std::stoi(next());
    else if (a == "--path") path = next();
    else if (a == "--view_depth") view_depth = std::stoi(next());
    else if (a == "--probe") probe = std::stoi(next());
    else if (a == "--trees_in") trees_in = next();
    else if (a == "--trees_out") trees_out = next();
    else if (a == "--codes") codes_arg = next();
    else if (a == "--pass_depth") pass_depth = std::stoi(next());
    else if (a == "--double") g_exact = false;
    else if (a == "--affine") g_affine = true;
    else if (a == "--blend") g_blend = true;
    else if (a == "--blend_contacts") g_blend_contacts = std::stoi(next());
    else if (a == "--code_jobs") code_jobs = std::stoi(next());
    else if (a == "--mu_guard") g_mu_guard = true;
    else if (a == "--affine_gap") g_affine_gap = std::stoi(next());
    else if (a == "--max_leaves") max_leaves = std::stoll(next());
    else if (a == "--bdd") bdd = next();
    else if (a == "--rho") rho = Q(std::string_view(next()));
    else if (a == "--max_depth") max_depth = std::stoi(next());
    else if (a == "--try") g_try = std::stoi(next());
    else if (a == "--threads") g_max_active = 2 * std::stoi(next());
    else if (a == "--faces") {
      const std::string s = next();
      size_t p = 0;
      while (p < s.size()) {
        size_t q = s.find(',', p);
        if (q == std::string::npos) q = s.size();
        const std::string f = s.substr(p, q - p);
        const size_t colon = f.find(':');
        CHECK(colon != std::string::npos) << f;
        charts.push_back({std::stoi(f.substr(0, colon)), std::stoi(f.substr(colon + 1)) > 0});
        p = q + 1;
      }
    } else LOG(FATAL) << "unknown argument " << a;
  }
  CHECK(view.size() == 3 || code >= 0 || !trees_in.empty()) << "--view x,y,z, --code C --tri T or --trees_in DIR";
  if (charts.empty())
    for (int ax = 0; ax < 3; ax++) for (bool s : {true, false}) charts.push_back({ax, s});

  Setup st;
  st.rho = rho;
  for (int v = 0; v < NUM_VERTICES; v++) {
    const BigVecQ3 &q = VertexQ(v);
    st.VQ.push_back({q.x, q.y, q.z});
    st.V.push_back(ToD(st.VQ.back()));
  }
  if (!trees_in.empty()) {
    // The tree pass over every code's tube tree (or --codes).
    CHECK(!trees_out.empty() && trees_out != trees_in) << "--trees_out DIR (not --trees_in)";
    std::filesystem::create_directories(trees_out);
    rapidjson::Document doc;
    const std::string content = Util::ReadFile(bdd);
    doc.Parse(content.c_str());
    CHECK(!doc.HasParseError() && doc.HasMember("codes")) << bdd;
    const int ncodes = doc["codes"].GetArray().Size();
    std::vector<bool> want(ncodes, codes_arg.empty());
    for (double c : ParseDoubles(codes_arg)) want[(int)c] = true;
    PassStats total;
    const auto t0 = std::chrono::steady_clock::now();
    // Codes are independent (one tree file each): --code_jobs of them at
    // once, the slowest (most tube leaves) first; each code's log is
    // printed when it is done.
    std::mutex out_mu;
    std::atomic<int> next{0};
    std::vector<int> order(ncodes);
    for (int c = 0; c < ncodes; c++) order[c] = c;
    if (code_jobs > 1) {
      std::vector<int64_t> size(ncodes, 0);
      for (int c = 0; c < ncodes; c++)
        if (want[c]) size[c] = std::filesystem::file_size(trees_in + "/tree." + std::to_string(c) + ".json");
      std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return size[a] > size[b]; });
    }
    auto Worker = [&]() {
      for (int i; (i = next++) < ncodes;) {
        const int c = order[i];
        const std::string in = trees_in + "/tree." + std::to_string(c) + ".json";
        std::unique_ptr<tubetree::CodeTree> tree = tubetree::LoadCodeTreeJson(in);
        CHECK(tree != nullptr) << in;
        if (want[c]) {
          PassStats ps;
          for (auto &ct : tree->triangles)
            Pass(st, ct.root.get(), ct.triangle, pass_depth, charts, max_depth, max_leaves, &ps);
          std::lock_guard<std::mutex> l(out_mu);
          printf("code %d:\n%scode %d: %lld nodes tried, %lld replaced (%lld certificate leaves for %lld tube leaves)\n",
                 c, ps.log.c_str(), c, (long long)ps.tried, (long long)ps.replaced, (long long)ps.cert_leaves,
                 (long long)ps.removed_leaves);
          total.tried += ps.tried;
          total.replaced += ps.replaced;
          total.cert_leaves += ps.cert_leaves;
          total.removed_leaves += ps.removed_leaves;
        }
        CHECK(tubetree::SaveCodeTreeJson(*tree, trees_out + "/tree." + std::to_string(c) + ".json"));
      }
    };
    std::vector<std::thread> workers;
    for (int j = 0; j < std::max(1, code_jobs); j++) workers.emplace_back(Worker);
    for (std::thread &w : workers) w.join();
    printf("pass: %lld nodes replaced (%lld certificate leaves for %lld tube leaves), %.1f s\n",
           (long long)total.replaced, (long long)total.cert_leaves, (long long)total.removed_leaves,
           std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
    return 0;
  }
  tubetree::TriangleQ start;
  if (code >= 0) {
    // Code C's triangle T, subdivided along the path.
    rapidjson::Document doc;
    const std::string content = Util::ReadFile(bdd);
    doc.Parse(content.c_str());
    CHECK(!doc.HasParseError() && doc.HasMember("codes")) << bdd;
    const auto &codes = doc["codes"].GetArray();
    CHECK(code < (int)codes.Size()) << "code " << code;
    const auto &tris = codes[code]["triangles"].GetArray();
    CHECK(tri < (int)tris.Size()) << "triangle " << tri;
    tubetree::TriangleQ t;
    for (int k = 0; k < 3; k++) {
      const auto &cv = tris[tri][k];
      t.corners[k] = {Q(std::string_view(cv["x"].GetString())), Q(std::string_view(cv["y"].GetString())),
                      Q(std::string_view(cv["z"].GetString()))};
    }
    for (char d : path) {
      CHECK(d >= '0' && d <= '3') << path;
      tubetree::TriangleQ ch4[4];
      t.Subdivide(ch4);
      t = ch4[d - '0'];
    }
    for (int k = 0; k < 3; k++) st.c[k] = {t.corners[k].x, t.corners[k].y, t.corners[k].z};
    start = t;
    V3<double> m{0, 0, 0};
    for (int k = 0; k < 3; k++) m = Add(m, ToD(st.c[k]));
    view = {m[0], m[1], m[2]};
    size = 0;
    for (int i = 0; i < 3; i++)
      for (int j = i + 1; j < 3; j++) {
        const V3<double> a = ToD(st.c[i]), b = ToD(st.c[j]);
        size = std::max(size, std::acos(std::clamp(Dot(a, b) / (Norm(a) * Norm(b)), -1.0, 1.0)));
      }
  } else {
  // The view triangle: equilateral, centered at the view, in the projective
  // chart sum_c sign(u_c) u_c = 1, of angular diameter `size` (as tubeprobe).
    double n = std::sqrt(view[0] * view[0] + view[1] * view[1] + view[2] * view[2]);
    const V3<double> u{view[0] / n, view[1] / n, view[2] / n};
    const V3<double> sg{u[0] >= 0 ? 1.0 : -1.0, u[1] >= 0 ? 1.0 : -1.0, u[2] >= 0 ? 1.0 : -1.0};
    const V3<double> p = Scale(1 / Dot(sg, u), u);
    V3<double> a = Cross(sg, {0, 0, 1});
    if (Norm(a) < 0.1) a = Cross(sg, {1, 0, 0});
    a = Scale(1 / Norm(a), a);
    const V3<double> b = Scale(1 / Norm(Cross(sg, a)), Cross(sg, a));
    const double s = size * Norm(p) / std::sqrt(3.0);
    for (int k = 0; k < 3; k++) {
      const double th = 2 * M_PI * k / 3 + 0.1;
      const V3<double> c = Add(p, Scale(s, Add(Scale(std::cos(th), a), Scale(std::sin(th), b))));
      // Corners to 2^-40.
      for (int i = 0; i < 3; i++) st.c[k][i] = DyadicRat(std::ldexp(std::round(std::ldexp(c[i], 40)), -40));
    }
  }
  printf("view (%.6f, %.6f, %.6f), triangle size %.1e, rho %s, %zu charts\n", view[0], view[1], view[2], size,
         rho.ToString().c_str(), charts.size());
  if (probe > 0) {
    Probe(st, probe);
    return 0;
  }
  const auto t0 = std::chrono::steady_clock::now();
  if (view_depth >= 0) {
    CHECK(code >= 0) << "--view_depth needs --code";
    TreeStats ts;
    ViewTree(st, start, path, 0, view_depth, charts, max_depth, max_leaves, &ts);
    printf("%s: %lld view leaves (depth <= %d), %lld certificate leaves, %lld failed, %.1f s\n",
           ts.failed == 0 ? "OK" : "FAILED", (long long)ts.view_leaves, ts.max_depth, (long long)ts.cert_leaves,
           (long long)ts.failed, std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
    return ts.failed == 0 ? 0 : 1;
  }
  int64_t total = 0;
  const bool all_ok = CertifyTriangle(st, charts, max_depth, max_leaves, &total, true);
  printf("%s: %lld leaves in %.1f s\n", all_ok ? "OK" : "FAILED", (long long)total,
         std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
  return all_ok ? 0 : 1;
}
