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
//   view      u = c0 + alpha (c1 - c0) + beta (c2 - c0)  (a parallelogram
//             containing T; d_k = u x c_k is perpendicular to u whatever its
//             scale)
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

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <future>
#include <memory>
#include <mutex>
#include <string>
#include <vector>

#include "base/logging.h"
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

template <class T> Chart<T> MakeChart(const Setup &st, const ChartId &id) {
  using P = PolyT<T>;
  const V3<T> c0 = ToTV<T>(st.c[0]), c1 = ToTV<T>(st.c[1]), c2 = ToTV<T>(st.c[2]);
  Chart<T> ch;
  ch.u = PConst(c0) + (P::Var(1) * PConst(VSub(c1, c0)) + P::Var(2) * PConst(VSub(c2, c0)));
  PV<T> sigma;
  int free = 3;
  for (int i = 0; i < 3; i++)
    sigma[i] = i == id.axis ? P::Const(FromQ<T>(Q(id.sign ? 1 : -1))) : P::Var(free++);
  ch.w = P::Var(0) * sigma;
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
};

struct Stats { std::atomic<int64_t> ok{0}, failed{0}; std::atomic<int> max_depth{0}; };

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

  Certifier(const Setup &s, const ChartId &i, int md, Stats *stt)
      : st(s), id(i), chart_box(ChartBox(s)), max_depth(md), stats(stt), ch(MakeChart<double>(s, i)) {}

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
  double Score(const Witness &W, const Box &box, Leaf *leaf = nullptr, std::string *why = nullptr) {
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
    for (int k = 0; k < K; k++) { ntup *= S[k].size(); ninner *= I[k].size(); }
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
    if (leaf) leaf->inner.clear();
    double score = 1e300;
    for (int64_t tix = 0; tix < ntup; tix++) {
      int64_t r = tix;
      std::vector<int> jt(K);
      for (int k = 0; k < K; k++) { jt[k] = S[k][r % S[k].size()]; r /= S[k].size(); }
      double best = kFail;
      std::vector<int> best_it;
      for (int64_t ci = 0; ci < ninner; ci++) {
        int64_t q = ci;
        std::vector<int> it(K);
        for (int k = 0; k < K; k++) { it[k] = I[k][q % I[k].size()]; q /= I[k].size(); }
        PolyT<double> Pp;
        for (int k = 0; k < K; k++) Pp = Pp + (Aof(k, it[k]) - Bof(k, jt[k]));
        const double bnd = BernsteinLowerD(Reduce(Pp), box);
        if (bnd > best) { best = bnd; best_it = it; }
      }
      score = std::min(score, best);
      if (best < -1e-13) {
        if (why) {
          *why = "tuple (outer";
          for (int j : jt) *why += " " + std::to_string(j);
          *why += ") best bound " + std::to_string(best);
        }
        if (!leaf) continue;
        return score;
      }
      if (leaf) leaf->inner.push_back(best_it);
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

  // Returns the number of leaves of the subtree (0: failed).
  int64_t Rec(Box box, int depth, bool *ok) {
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
    // (At mu = 0 every witness has value 0: sample at the box's top mu.)
    for (auto &x : pts) if (x[0] == 0) x[0] = box[0].second;
    std::vector<Witness> cands;
    for (int pi : {0, 3, 5, 7, 9}) {
      const Pose q = PoseAt(ch, pts[pi].data());
      for (Witness &w : Combine(st, ContactPool(st, q), q, pi == 0 ? 24 : 8)) cands.push_back(std::move(w));
    }
    std::vector<std::pair<double, int>> sc;
    for (int wi = 0; wi < (int)cands.size(); wi++) {
      double worst = 1e300;
      for (const auto &x : pts) worst = std::min(worst, Value(st, cands[wi], PoseAt(ch, x.data())));
      sc.push_back({worst, wi});
    }
    std::sort(sc.begin(), sc.end(), [](auto &a, auto &b) { return a.first > b.first; });
    const int ntry = std::min<int>(g_try, sc.size());
    for (int r = 0; r < ntry; r++) {
      if (sc[r].first <= 0) break;
      Leaf leaf;
      if (!Check(cands[sc[r].second], box, &leaf)) continue;
      stats->ok++;
      *ok = true;
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
      return 0;
    }
    // Split the variable whose halves have the best worse-half score for the
    // best few candidates (the score: Score above, the quantity the leaf
    // check needs); without candidates, the widest variable relative to the
    // chart's box.
    int best = -1;
    double bw = -1e301;
    const double cur = sc.empty() ? -1e300 : Score(cands[sc[0].second], box);
    for (int r = 0; r < std::min<int>(3, sc.size()); r++) {
      const Witness &W = cands[sc[r].second];
      for (int i = 0; i < NV; i++) {
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
      best = 0;
      bw = -1;
      for (int i = 0; i < NV; i++) {
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
    if (g_active.load() < g_max_active) {
      g_active++;
      auto fut = std::async(std::launch::async, [&]() { return Rec(b2, depth + 1, &ok2); });
      n1 = Rec(b1, depth + 1, &ok1);
      n2 = fut.get();
      g_active--;
    } else {
      n1 = Rec(b1, depth + 1, &ok1);
      n2 = Rec(b2, depth + 1, &ok2);
    }
    *ok = ok1 && ok2;
    return n1 + n2;
  }
};

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
  std::vector<double> view;
  double size = 1e-3;
  int code = -1, tri = 0;
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
  CHECK(view.size() == 3 || code >= 0) << "--view x,y,z or --code C --tri T";
  if (charts.empty())
    for (int ax = 0; ax < 3; ax++) for (bool s : {true, false}) charts.push_back({ax, s});

  Setup st;
  st.rho = rho;
  for (int v = 0; v < NUM_VERTICES; v++) {
    const BigVecQ3 &q = VertexQ(v);
    st.VQ.push_back({q.x, q.y, q.z});
    st.V.push_back(ToD(st.VQ.back()));
  }
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
  int64_t total = 0;
  bool all_ok = true;
  const auto t0 = std::chrono::steady_clock::now();
  for (const ChartId &id : charts) {
    Stats stats;
    Certifier cert(st, id, max_depth, &stats);
    bool ok = false;
    const auto t1 = std::chrono::steady_clock::now();
    const int64_t n = cert.Rec(ChartBox(st), 0, &ok);
    const double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count();
    printf("  face %-5s %s  leaves %lld  failed %lld  depth %d  (%.1f s)\n", id.Name().c_str(), ok ? "OK  " : "FAIL",
           (long long)n, (long long)stats.failed.load(), stats.max_depth.load(), sec);
    for (const std::string &f : cert.fail_boxes) printf("    failed box %s\n", f.c_str());
    total += n;
    all_ok = all_ok && ok;
  }
  printf("%s: %lld leaves in %.1f s\n", all_ok ? "OK" : "FAILED", (long long)total,
         std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
  return all_ok ? 0 : 1;
}
