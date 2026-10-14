// kcapq: exact cap certificates (Lean Pipeline/KCapCheck, KCapTree) for a
// solid with rational vertices (model.h) at a view x where two face planes
// are edge-on at once: a codimension-2 view, where the best inner witness
// vertex switches at a rotation size proportional to the distance from x, so
// that no box subdivision in (view, rotation) ends there (the Septopert's
// corner of code triangle t9; nopert229/notes/SEPTOPERT-IMPROVEMENTS.md).
// The view and the rotation are blown up together, as in the snub cube's cap
// (search/sc/sccapcert.cc, of which this is the rational-model version: the
// same charts, witnesses, exact checks over Q(t) (rationals have zero
// t-parts, so Lean's KCap decoder and check apply unchanged) and export).
//
// The frame: x = n_1 x n_2 (the faces' normals, oriented toward --near),
// e1 = x x n_1 (the tangent at x of face 1's edge-on circle: the chart line
// tau = 0), e2 = L (x x e1) with L rational so that face 2's circle is the
// chart line tau = 1/2 (on sides 0, 1, or 2, 3 for |tau| > 1); the rotation
// frame Z, E1, X: x, e1, x x e1 scaled to about unit length. x, e1 are scaled
// to about unit length too, so mu0 is about an angle.
//
// The tie charts (tcone, the snub cube's exact tie) are kept with
// tie_s0 = 0 (a cone around the identity on side 1): Lean's KCert.check
// requires them; here they only cover poses the other charts cover too.
//
// Usage: kcapq.exe --faces a,b,c:d,e,f --near x,y,z [--mu0 1/64] [--R 2]
//          [--t0 1/4] [--max_depth 40] [--threads 64] [--try 16]
//          [--only kind:side:axis:sign,...] [--export FILE] [--caps FILE] [--double]

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <future>
#include <map>
#include <memory>
#include <mutex>
#include <sstream>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"
#include "kpoly.h"
#include "model.h"

// Q(t) arithmetic (in exact5d, for argument-dependent lookup from kpoly's
// templates) and Q(t) as a kpoly scalar.
namespace exact5d {
inline TQ operator+(const TQ &x, const TQ &y) { return TAdd(x, y); }
inline TQ operator-(const TQ &x, const TQ &y) { return TSub(x, y); }
inline TQ operator-(const TQ &x) { return {BigRat(0) - x.a, BigRat(0) - x.b, BigRat(0) - x.c}; }
inline TQ operator*(const TQ &x, const TQ &y) { return TMul(x, y); }
}  // namespace exact5d

template <> inline bool kpoly::IsZeroT<exact5d::TQ>(const exact5d::TQ &x) {
  return x.a == BigRat(0) && x.b == BigRat(0) && x.c == BigRat(0);
}
template <> inline exact5d::TQ kpoly::One<exact5d::TQ>() { return {BigRat(1), BigRat(0), BigRat(0)}; }
template <> inline exact5d::TQ kpoly::FromQ<exact5d::TQ>(const BigRat &q) { return {q, BigRat(0), BigRat(0)}; }

namespace {

using namespace kpoly;
using exact5d::TQ;

int g_try = 16;
bool g_double = false;

// ----- Q(t) -----
TQ TOf(int a) { return {Q(a), Q(0), Q(0)}; }
TQ TOfQ(const Q &a) { return {a, Q(0), Q(0)}; }
bool IsZero(const TQ &x) { return x.a == Q(0) && x.b == Q(0) && x.c == Q(0); }
TQ TInv(const TQ &x) {
  // Solve x y = 1: the 3x3 linear system of multiplication by x on (1, t, t^2).
  // Columns: x * 1, x * t, x * t^2.
  const TQ cols[3] = {x, x * TQ{Q(0), Q(1), Q(0)}, x * TQ{Q(0), Q(0), Q(1)}};
  Q m[3][4];
  for (int r = 0; r < 3; r++) {
    for (int c = 0; c < 3; c++) m[r][c] = r == 0 ? cols[c].a : r == 1 ? cols[c].b : cols[c].c;
    m[r][3] = r == 0 ? Q(1) : Q(0);
  }
  for (int c = 0; c < 3; c++) {
    int p = c;
    while (m[p][c] == Q(0)) p++;
    for (int k = 0; k < 4; k++) std::swap(m[c][k], m[p][k]);
    const Q inv = Q(1) / m[c][c];
    for (int k = 0; k < 4; k++) m[c][k] = m[c][k] * inv;
    for (int r = 0; r < 3; r++) {
      if (r == c || m[r][c] == Q(0)) continue;
      const Q f = m[r][c];
      for (int k = 0; k < 4; k++) m[r][k] = m[r][k] - f * m[c][k];
    }
  }
  const TQ y{m[0][3], m[1][3], m[2][3]};
  CHECK(IsZero(x * y - TOf(1)));
  return y;
}
double TD(const TQ &x) { return exact5d::TDouble(x); }

// ----- Q(t) intervals -----
Iv kT, kT2;
void InitConstants() {
  const Q lo(std::string_view("1839286755214161/1000000000000000")), hi(std::string_view("1839286755214162/1000000000000000"));
  auto f = [](const Q &x) { return x * x * x - x * x - x - Q(1); };
  CHECK(Q::Sign(f(lo)) < 0 && Q::Sign(f(hi)) > 0);
  kT = {Dn(lo.ToDouble()), Up(hi.ToDouble())};
  kT2 = kT * kT;
}
Iv IvOfT(const TQ &x) {
  if (IsZero(x)) return IvOf(0);
  return IvOfQ(x.a) + IvOfQ(x.b) * kT + IvOfQ(x.c) * kT2;
}

struct TOps {
  TQ zero() const { return TOf(0); }
  TQ add(const TQ &a, const TQ &b) const { return a + b; }
  bool is_zero(const TQ &a) const { return IsZero(a); }
  TQ scale(const Q &q, const TQ &a) const { return exact5d::TScale(q, a); }
};

// The exact check: Lean's KPoly.lowerDeg (the minimum of TribQ.lo over the
// exact Bernstein coefficients) compared with `bound` (>= 0, or > 0 when
// strict). The outward-rounded interval coefficients decide first.
bool ExactLowerOk(const PolyT<TQ> &p, const std::array<std::pair<Q, Q>, NV> &box, bool strict) {
  const std::array<int, NV> deg = Degrees(p);
  std::map<Exp, Iv> ti;
  bool any = false;
  for (const auto &[e, c] : p.t) if (!IsZero(c)) { ti[e] = IvOfT(c); any = true; }
  if (!any) return !strict;  // the zero polynomial: lowerDeg = 0
  const std::vector<Iv> iv = Bernstein(ti, deg, box, IvOps());
  double m = INFINITY;
  for (const Iv &x : iv) m = std::min(m, x.lo);
  if (strict ? m > 0 : m >= 0) return true;
  std::map<Exp, TQ> tt;
  for (const auto &[e, c] : p.t) if (!IsZero(c)) tt[e] = c;
  const std::vector<TQ> ex = Bernstein(tt, deg, box, TOps());
  for (const TQ &x : ex) {
    const int s = Q::Sign(exact5d::TLower(x));
    if (strict ? s <= 0 : s < 0) return false;
  }
  return true;
}

// ----- The solid and the frame -----
struct Setup {
  std::vector<V3<TQ>> VT;
  std::vector<V3<double>> V;
  // x, e1, e2, Z, E1, X.
  std::array<V3<TQ>, 6> FT;
  std::array<V3<double>, 6> F;
  TQ L2;
  Q mu0{1, 64}, R{2}, t0{1, 4}, tie_s0{0}, tie_t0{1, 4}, tie_mu0{1, 64};
  int tie_side = 1;
};

V3<double> ToD(const V3<TQ> &v) { return {TD(v[0]), TD(v[1]), TD(v[2])}; }

// A rational as an element of Q(t).
TQ TQOf(const Q &q) { return {q, Q(0), Q(0)}; }
V3<TQ> TQV(const V3<Q> &v) { return {TQOf(v[0]), TQOf(v[1]), TQOf(v[2])}; }
V3<Q> QCross(const V3<Q> &a, const V3<Q> &b) { return VCross(a, b); }
Q QDot(const V3<Q> &a, const V3<Q> &b) { return VDot(a, b); }
// v scaled by a rational close to 1 / |v| (a multiple of 1/64).
V3<Q> RoughUnit(const V3<Q> &v) {
  const double n = std::sqrt(QDot(v, v).ToDouble());
  const Q s(std::max<int64_t>(1, std::llround(64.0 / n)), 64);
  return {v[0] * s, v[1] * s, v[2] * s};
}

void MakeSolid(Setup *st, const int f1[3], const int f2[3], const V3<double> &near) {
  std::vector<V3<Q>> VQ;
  for (int v = 0; v < NUM_VERTICES; v++) {
    const BigVecQ3 &q = VertexQ(v);
    VQ.push_back({q.x, q.y, q.z});
    st->VT.push_back(TQV(VQ.back()));
    st->V.push_back(ToD(st->VT.back()));
  }
  auto normal = [&](const int f[3]) {
    return QCross(VSub(VQ[f[1]], VQ[f[0]]), VSub(VQ[f[2]], VQ[f[0]]));
  };
  const V3<Q> n1 = normal(f1), n2 = normal(f2);
  V3<Q> x = QCross(n1, n2);
  if (x[0].ToDouble() * near[0] + x[1].ToDouble() * near[1] + x[2].ToDouble() * near[2] < 0)
    x = {Q(0) - x[0], Q(0) - x[1], Q(0) - x[2]};
  x = RoughUnit(x);
  const V3<Q> e1 = RoughUnit(QCross(x, n1));
  const V3<Q> e2p = QCross(x, e1);
  // Face 2's circle: tangent t = n2 x x; tau' = (t.e2'/|e2'|^2) / (t.e1/|e1|^2).
  const V3<Q> t2 = QCross(n2, x);
  const Q a = QDot(t2, e1) / QDot(e1, e1), b = QDot(t2, e2p) / QDot(e2p, e2p);
  CHECK(!(a == Q(0))) << "face 2's circle is tangent to e2";
  Q tau = b / a;
  if (Q::Sign(tau) < 0) tau = Q(0) - tau;
  // e2 = L e2' with tau' / L = 1/2.
  const Q L = tau * Q(2);
  const V3<Q> e2 = {e2p[0] * L, e2p[1] * L, e2p[2] * L};
  const V3<Q> Xr = RoughUnit(QCross(x, e1));
  st->FT = {TQV(x), TQV(e1), TQV(e2), TQV(x), TQV(e1), TQV(Xr)};
  for (int f = 0; f < 6; f++) st->F[f] = ToD(st->FT[f]);
  st->L2 = TQOf(L);
  printf("x = (%.6f, %.6f, %.6f) (unit %.6f), circle 2 at tau = %s before scaling, L = %.6f\n",
         st->F[0][0], st->F[0][1], st->F[0][2], std::sqrt(VDot(st->F[0], st->F[0])), tau.ToString().c_str(),
         L.ToDouble());
}

// ----- Charts (Lean KCapChart) -----
enum class Kind { fe, face, cone, tcone };
struct ChartId {
  Kind kind = Kind::fe;
  int side = 0, axis = 0;
  bool sign = true;
  Box box;
  std::string Name() const {
    const char *k[] = {"fe", "face", "cone", "tcone"};
    return std::string(k[(int)kind]) + ":" + std::to_string(side) + ":" + std::to_string(axis) + ":" +
           (sign ? "1" : "-1");
  }
};

template <class T> struct Chart { PV<T> u, w; PolyT<T> D; std::vector<PV<T>> NV_; };

template <class T> T ToT(const TQ &x);
template <> double ToT<double>(const TQ &x) { return TD(x); }
template <> TQ ToT<TQ>(const TQ &x) { return x; }
template <class T> V3<T> ToTV(const V3<TQ> &v) { return {ToT<T>(v[0]), ToT<T>(v[1]), ToT<T>(v[2])}; }

template <class T> Chart<T> MakeChart(const Setup &st, const ChartId &id) {
  using P = PolyT<T>;
  auto var = [](int i) { return P::Var(i); };
  auto cq = [](const Q &q) { return P::Const(FromQ<T>(q)); };
  const Q sgn(id.sign ? 1 : -1);
  // faceCoord first axis sign c i: the fixed coordinate or the next free variable.
  auto faceCoord = [&](int first, const Q &c, int i) {
    if (i == id.axis) return cq(sgn * c);
    return var(std::min(4, i < id.axis ? first + i : first + i - 1));
  };
  P e = P::Const(One<T>()), tau = var(1);
  P s[3];
  switch (id.kind) {
    case Kind::fe:
      for (int i = 0; i < 3; i++) s[i] = var(2 + i);
      break;
    case Kind::face:
      e = var(2);
      for (int i = 0; i < 3; i++) s[i] = faceCoord(3, st.R, i);
      break;
    case Kind::cone:
      for (int i = 0; i < 3; i++) s[i] = cq(st.R / Q(2)) * (var(2) * faceCoord(3, Q(1), i));
      break;
    case Kind::tcone: {
      P sig[4];
      for (int i = 0; i < 4; i++) sig[i] = faceCoord(2, Q(1), i);
      tau = var(1) * sig[0];
      s[0] = cq(st.tie_s0) + var(1) * sig[1];
      s[1] = var(1) * sig[2];
      s[2] = var(1) * sig[3];
      break;
    }
  }
  const V3<T> e1 = ToTV<T>(st.FT[1]), e2 = ToTV<T>(st.FT[2]);
  V3<T> A, B;
  auto neg = [](const V3<T> &v) { return V3<T>{T() - v[0], T() - v[1], T() - v[2]}; };
  switch (id.side) {
    case 0: A = e1; B = e2; break;
    case 1: A = neg(e1); B = e2; break;
    case 2: A = e2; B = e1; break;
    default: A = neg(e2); B = e1; break;
  }
  Chart<T> ch;
  ch.u = PConst(ToTV<T>(st.FT[0])) + (var(0) * e) * (PConst(A) + tau * PConst(B));
  ch.w = var(0) * (s[0] * PConst(ToTV<T>(st.FT[3])) + (s[1] * PConst(ToTV<T>(st.FT[4])) + s[2] * PConst(ToTV<T>(st.FT[5]))));
  const P ww = PDot(ch.w, ch.w);
  ch.D = P::Const(One<T>()) + ww;
  const std::vector<V3<TQ>> &VT = st.VT;
  for (const V3<TQ> &vq : VT) {
    const V3<T> v = ToTV<T>(vq);
    const PV<T> cv = PConst(v);
    // N(w) v = (1 - |w|^2) v + 2 (w.v) w + 2 w x v (Lean cayleyNum).
    const P two = P::Const(One<T>() + One<T>());
    ch.NV_.push_back((P::Const(One<T>()) - ww) * cv + ((two * PDot(ch.w, cv)) * ch.w + two * PCross(ch.w, cv)));
  }
  return ch;
}

// ----- Poses and witnesses (double) -----
struct Pose { V3<double> u, w; };
Pose PoseAt(const Chart<double> &ch, const double *y) {
  Pose q;
  for (int a = 0; a < 3; a++) { q.u[a] = Eval(ch.u[a], y); q.w[a] = Eval(ch.w[a], y); }
  return q;
}
V3<double> Add(const V3<double> &a, const V3<double> &b) { return {a[0] + b[0], a[1] + b[1], a[2] + b[2]}; }
V3<double> Sub(const V3<double> &a, const V3<double> &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
V3<double> Scale(double s, const V3<double> &a) { return {s * a[0], s * a[1], s * a[2]}; }
double Dot(const V3<double> &a, const V3<double> &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
V3<double> Cross(const V3<double> &a, const V3<double> &b) { return VCross(a, b); }
double Norm(const V3<double> &a) { return std::sqrt(Dot(a, a)); }
V3<double> Rot(const V3<double> &w, const V3<double> &v) {
  const double ww = Dot(w, w);
  const V3<double> wv = Cross(w, v);
  V3<double> r;
  for (int a = 0; a < 3; a++) r[a] = ((1 - ww) * v[a] + 2 * w[a] * Dot(w, v) + 2 * wv[a]) / (1 + ww);
  return r;
}

// A contact: the edge direction c = V[b] - V[a], its x-support set (the
// vertices maximal along x x c), its best inner vertex at the pose.
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

double Value(const Setup &st, const Witness &W, const Pose &q) {
  const std::vector<double> l = Weights(W, q);
  double sl = 0;
  for (double x : l) { if (x < 0) return -1e300; sl += x; }
  if (sl <= 0) return -1e300;
  double s = 0;
  for (size_t k = 0; k < W.k.size(); k++) {
    const Contact &c = W.k[k];
    const V3<double> d = Cross(q.u, c.c);
    double h = -1e300;
    for (const auto &v : st.V) h = std::max(h, Dot(v, d));
    s += l[k] * (Dot(Rot(q.w, st.V[c.i]), d) - h);
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

void Frame2(const V3<double> &u0, V3<double> *f, V3<double> *g) {
  const V3<double> u = Scale(1 / Norm(u0), u0);
  *f = Scale(1 / Norm(Cross({0, 0, 1}, u)), Cross({0, 0, 1}, u));
  *g = Cross(u, *f);
}

// The contact pool at a pose: the edge vectors of the shadow's hull edges.
std::vector<Contact> ContactPool(const Setup &st, const Pose &q) {
  std::vector<Contact> pool;
  V3<double> f, g;
  Frame2(q.u, &f, &g);
  const int n = st.V.size();
  std::vector<std::array<double, 2>> P(n);
  for (int i = 0; i < n; i++) P[i] = {Dot(st.V[i], f), Dot(st.V[i], g)};
  const std::vector<int> H = Hull2(P, 1e-14);
  const V3<double> &x = st.F[0];
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
    const V3<double> dx0 = Cross(x, c.c);
    if (Norm(dx0) < 1e-12) continue;
    c.S = SupportSet(st, dx0);
    const V3<double> d = Cross(q.u, c.c);
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
    o.S = SupportSet(st, Cross(st.F[0], o.c));
    const V3<double> dd = Cross(q.u, o.c);
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
// A checked leaf: the witness (contacts as edges, sign), the outer sets S_k
// (after dominance), and per tuple the inner choices.
struct Leaf {
  int K = 0, s = 1;
  std::vector<std::pair<int, int>> edges;
  std::vector<std::vector<int>> S;
  std::vector<std::vector<int>> inner;  // per tuple, K inner indices
};

std::string LeafString(const Leaf &l) {
  std::string r = "l " + std::to_string(l.K) + " " + std::to_string(l.s);
  for (int k = 0; k < l.K; k++) {
    r += " " + std::to_string(l.edges[k].first) + " " + std::to_string(l.edges[k].second) + " " +
         std::to_string(l.S[k].size());
    for (int j : l.S[k]) r += " " + std::to_string(j);
  }
  r += " " + std::to_string(l.inner.size());
  for (const auto &it : l.inner)
    for (int i : it) r += " " + std::to_string(i);
  return r;
}

struct Node {
  int axis = -1;  // split axis, or -1
  std::unique_ptr<Node> l, r;
  std::string leaf;  // "l ..." or "c" (covered by the cone charts)
};
void Serialize(const Node &n, std::string *out) {
  if (n.axis >= 0) {
    *out += "s " + std::to_string(n.axis) + "\n";
    Serialize(*n.l, out);
    Serialize(*n.r, out);
  } else {
    *out += n.leaf + "\n";
  }
}

struct Stats { std::atomic<int64_t> ok{0}, failed{0}, cone{0}, exact_fail{0}, exact_fallback{0}; };

std::atomic<int> g_active{0};
int g_max_active = 128;

struct Certifier {
  const Setup &st;
  ChartId id;
  int max_depth;
  Stats *stats;
  Chart<double> ch;
  Chart<TQ> cht;
  std::mutex mu;
  std::vector<std::string> fail_boxes;

  Certifier(const Setup &s, const ChartId &i, int md, Stats *stt)
      : st(s), id(i), max_depth(md), stats(stt), ch(MakeChart<double>(s, i)) {
    if (!g_double) cht = MakeChart<TQ>(s, i);
  }

  bool Cone() const { return id.kind == Kind::cone; }
  bool TieCone() const { return id.kind == Kind::tcone; }

  // Lean: the F_e box inside the identity cone or (tie side) the tie cone.
  bool InCone(const Box &box) const {
    if (id.kind != Kind::fe) return false;
    auto within = [&](int v, double c, double rad) {
      return std::max(std::abs(box[v].first - c), std::abs(box[v].second - c)) <= rad;
    };
    const double rad = (st.t0 * st.R / Q(2)).ToDouble();
    if (within(2, 0, rad) && within(3, 0, rad) && within(4, 0, rad)) return true;
    if (id.side != st.tie_side) return false;
    const double tt = st.tie_t0.ToDouble(), s0 = st.tie_s0.ToDouble();
    return within(1, 0, tt) && within(2, s0, tt) && within(3, 0, tt) && within(4, 0, tt);
  }

  template <class T> PolyT<T> Reduce(PolyT<T> P) const {
    P = DivideVar(P, 0);
    if (Cone()) P = DivideVar(P, 2);
    if (TieCone()) P = DivideVar(P, 1);
    return P;
  }

  // The leaf's polynomials over T: weights, d_k, and the cached terms.
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

  // The double screen of witness W on the box; fills the leaf (outer sets,
  // inner choices) on success.
  bool Check(const Witness &W, const Box &box, Leaf *leaf) {
    const int K = W.k.size();
    std::vector<V3<double>> dirs;
    for (const Contact &c : W.k) dirs.push_back(c.c);
    const Parts<double> P = MakeParts(ch, dirs, W.s);
    if (K == 3)
      for (int k = 0; k < 3; k++) if (BernsteinLowerD(P.lam[k], box) < 0) return false;
    // Strictness: sum lambda_k |d_k|^2 > 0.
    {
      PolyT<double> sl;
      for (int k = 0; k < K; k++) sl = sl + PDot(P.L[k], P.d[k]);
      if (!(BernsteinLowerD(sl, box) > 0)) return false;
    }
    // Dominance.
    std::vector<std::vector<int>> S(K);
    for (int k = 0; k < K; k++) {
      S[k] = W.k[k].S;
      for (int j = 0; j < (int)st.V.size(); j++) {
        if (std::find(W.k[k].S.begin(), W.k[k].S.end(), j) != W.k[k].S.end()) continue;
        const PolyT<double> dom = PDot(P.d[k], Sub(st.V[W.k[k].S[0]], st.V[j]));
        if (BernsteinLowerD(dom, box) < 0) S[k].push_back(j);
      }
    }
    int64_t ntup = 1;
    for (int k = 0; k < K; k++) ntup *= S[k].size();
    if (ntup > 4096) return false;
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
    leaf->inner.clear();
    for (int64_t tix = 0; tix < ntup; tix++) {
      int64_t r = tix;
      std::vector<int> jt(K);
      for (int k = 0; k < K; k++) { jt[k] = S[k][r % S[k].size()]; r /= S[k].size(); }
      auto Try = [&](const std::vector<int> &it) {
        PolyT<double> Pp;
        for (int k = 0; k < K; k++) Pp = Pp + (Aof(k, it[k]) - Bof(k, jt[k]));
        return BernsteinLowerD(Reduce(Pp), box) >= -1e-13;
      };
      // Diagonal choice (the outer vertex where it is in the x-support set),
      // the contacts' own inner vertices, then every combination.
      std::vector<int> it(K), own(K);
      for (int k = 0; k < K; k++) {
        own[k] = W.k[k].i;
        const auto &xs = W.k[k].S;
        it[k] = std::find(xs.begin(), xs.end(), jt[k]) != xs.end() ? jt[k] : own[k];
      }
      bool ok = Try(it);
      if (!ok && it != own) { it = own; ok = Try(it); }
      if (!ok) {
        int64_t ncomb = 1;
        for (int k = 0; k < K; k++) ncomb *= W.k[k].S.size();
        for (int64_t ci = 0; ci < ncomb && !ok; ci++) {
          int64_t q = ci;
          for (int k = 0; k < K; k++) { it[k] = W.k[k].S[q % W.k[k].S.size()]; q /= W.k[k].S.size(); }
          ok = Try(it);
        }
      }
      if (!ok) return false;
      leaf->inner.push_back(it);
    }
    leaf->K = K;
    leaf->s = W.s;
    leaf->edges.clear();
    for (const Contact &c : W.k) leaf->edges.push_back({c.a, c.b});
    leaf->S = S;
    return true;
  }

  // The exact check of a screened leaf (the Lean check).
  bool Exact(const Leaf &leaf, const Box &box) {
    const auto bq = BoxQ(box);
    const int K = leaf.K;
    std::vector<V3<TQ>> dirs;
    for (const auto &[a, b] : leaf.edges) dirs.push_back(VSub(st.VT[b], st.VT[a]));
    const Parts<TQ> P = MakeParts(cht, dirs, leaf.s);
    if (K == 3)
      for (int k = 0; k < 3; k++) if (!ExactLowerOk(P.lam[k], bq, false)) return false;
    {
      PolyT<TQ> sl;
      for (int k = 0; k < K; k++) sl = sl + PDot(P.L[k], P.d[k]);
      if (!ExactLowerOk(sl, bq, true)) return false;
    }
    for (int k = 0; k < K; k++) {
      const auto &S = leaf.S[k];
      for (int j = 0; j < (int)st.VT.size(); j++) {
        if (std::find(S.begin(), S.end(), j) != S.end()) continue;
        if (!ExactLowerOk(PDot(P.d[k], VSub(st.VT[S[0]], st.VT[j])), bq, false)) return false;
      }
    }
    std::vector<std::map<int, PolyT<TQ>>> A(K), B(K);
    auto Aof = [&](int k, int i) -> const PolyT<TQ> & {
      auto it = A[k].find(i);
      if (it != A[k].end()) return it->second;
      return A[k][i] = PDot(cht.NV_[i], P.L[k]);
    };
    auto Bof = [&](int k, int j) -> const PolyT<TQ> & {
      auto it = B[k].find(j);
      if (it != B[k].end()) return it->second;
      return B[k][j] = cht.D * PDot(P.L[k], st.VT[j]);
    };
    int64_t ntup = 1;
    for (int k = 0; k < K; k++) ntup *= leaf.S[k].size();
    CHECK((int64_t)leaf.inner.size() == ntup);
    for (int64_t tix = 0; tix < ntup; tix++) {
      int64_t r = tix;
      PolyT<TQ> Pp;
      for (int k = 0; k < K; k++) {
        const int j = leaf.S[k][r % leaf.S[k].size()];
        r /= leaf.S[k].size();
        Pp = Pp + (Aof(k, leaf.inner[tix][k]) - Bof(k, j));
      }
      if (!ExactLowerOk(Reduce(Pp), bq, false)) return false;
    }
    return true;
  }

  std::unique_ptr<Node> Rec(Box box, int depth, bool *ok) {
    auto node = std::make_unique<Node>();
    if (InCone(box)) { stats->cone++; node->leaf = "c"; *ok = true; return node; }
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
    for (auto &x : pts) {
      if (x[0] == 0) x[0] = box[0].second;
      if (Cone() && x[2] == 0) x[2] = box[2].second;
      if (TieCone() && x[1] == 0) x[1] = box[1].second;
    }
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
      if (!g_double && !Exact(leaf, box)) { stats->exact_fail++; continue; }
      stats->ok++;
      node->leaf = LeafString(leaf);
      *ok = true;
      return node;
    }
    if (depth >= max_depth) {
      stats->failed++;
      std::lock_guard<std::mutex> l(mu);
      if (fail_boxes.size() < 6u) {
        std::string s;
        for (auto &[lo, hi] : box) s += std::to_string(lo) + ".." + std::to_string(hi) + " ";
        s += " best " + (sc.empty() ? std::string("none") : std::to_string(sc[0].first));
        fail_boxes.push_back(s);
      }
      node->leaf = "f";
      *ok = false;
      return node;
    }
    // The widest variable relative to the chart's box, mu (and the tie
    // cone's t) only when 8 times wider.
    int best = 0;
    double bw = -1;
    for (int i = 0; i < NV; i++) {
      const double rel = (box[i].second - box[i].first) / (id.box[i].second - id.box[i].first) /
                         (i == 0 || (i == 1 && TieCone()) ? 8 : 1);
      if (rel > bw) { bw = rel; best = i; }
    }
    const double m = 0.5 * (box[best].first + box[best].second);
    auto b1 = box, b2 = box;
    b1[best].second = m;
    b2[best].first = m;
    node->axis = best;
    bool ok1 = false, ok2 = false;
    if (g_active.load() < g_max_active) {
      g_active++;
      auto fut = std::async(std::launch::async, [&]() { return Rec(b2, depth + 1, &ok2); });
      node->l = Rec(b1, depth + 1, &ok1);
      node->r = fut.get();
      g_active--;
    } else {
      node->l = Rec(b1, depth + 1, &ok1);
      node->r = Rec(b2, depth + 1, &ok2);
    }
    *ok = ok1 && ok2;
    return node;
  }
};

Q ParseQ(const std::string &s) { return Q(std::string_view(s)); }

std::string TStr(const TQ &x) { return x.a.ToString() + " " + x.b.ToString() + " " + x.c.ToString(); }
std::string VStr(const V3<TQ> &v) { return TStr(v[0]) + " " + TStr(v[1]) + " " + TStr(v[2]); }

}  // namespace

int main(int argc, char **argv) {
  setvbuf(stdout, nullptr, _IOLBF, 0);
  InitConstants();
  Setup st;
  int max_depth = 40, threads = 64;
  std::string only, export_file, caps_file;
  int f1[3] = {-1, -1, -1}, f2[3] = {-1, -1, -1};
  V3<double> near{1, 0, 0};
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a;
      return argv[++i];
    };
    if (a == "--faces") {
      CHECK(std::sscanf(next().c_str(), "%d,%d,%d:%d,%d,%d", &f1[0], &f1[1], &f1[2], &f2[0], &f2[1], &f2[2]) == 6);
    } else if (a == "--near") {
      CHECK(std::sscanf(next().c_str(), "%lf,%lf,%lf", &near[0], &near[1], &near[2]) == 3);
    } else if (a == "--mu0") st.mu0 = st.tie_mu0 = ParseQ(next());
    else if (a == "--R") st.R = ParseQ(next());
    else if (a == "--t0") st.t0 = ParseQ(next());
    else if (a == "--tie_t0") st.tie_t0 = ParseQ(next());
    else if (a == "--tie_mu0") st.tie_mu0 = ParseQ(next());
    else if (a == "--max_depth") max_depth = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--try") g_try = std::stoi(next());
    else if (a == "--only") only = next();
    else if (a == "--export") export_file = next();
    else if (a == "--caps") caps_file = next();
    else if (a == "--double") g_double = true;
    else LOG(FATAL) << "unknown argument " << a;
  }
  g_max_active = 2 * threads;
  CHECK(f1[0] >= 0 && f2[0] >= 0) << "--faces a,b,c:d,e,f";
  MakeSolid(&st, f1, f2, near);

  if (!caps_file.empty()) {
    FILE *f = fopen(caps_file.c_str(), "w");
    CHECK(f != nullptr);
    std::string frame;
    for (int k = 0; k < 6; k++) frame += " " + VStr(st.FT[k]);
    fprintf(f, "# kcapq: kind mu0 R t0 s0, then x e1 e2 Z E1 X (a b c = a + b t + c t^2)\n");
    fprintf(f, "0 %s %s 0 0%s\n", st.mu0.ToString().c_str(), st.R.ToString().c_str(), frame.c_str());
    fprintf(f, "1 %s 0 %s %s%s\n", st.tie_mu0.ToString().c_str(), st.tie_t0.ToString().c_str(),
            st.tie_s0.ToString().c_str(), frame.c_str());
    fclose(f);
    printf("wrote %s\n", caps_file.c_str());
  }

  const double mu0 = st.mu0.ToDouble(), R = st.R.ToDouble(), t0 = st.t0.ToDouble();
  std::vector<ChartId> charts;
  for (int side = 0; side < 4; side++) {
    ChartId fe;
    fe.kind = Kind::fe;
    fe.side = side;
    fe.box = {{{0, mu0}, {-1, 1}, {-R, R}, {-R, R}, {-R, R}}};
    charts.push_back(fe);
    for (int axis = 0; axis < 3; axis++)
      for (bool sign : {true, false}) {
        ChartId f;
        f.kind = Kind::face;
        f.side = side; f.axis = axis; f.sign = sign;
        f.box = {{{0, mu0}, {-1, 1}, {0, 1}, {-R, R}, {-R, R}}};
        charts.push_back(f);
        ChartId c = f;
        c.kind = Kind::cone;
        c.box = {{{0, mu0}, {-1, 1}, {0, t0}, {-1, 1}, {-1, 1}}};
        charts.push_back(c);
      }
  }
  for (int axis = 0; axis < 4; axis++)
    for (bool sign : {true, false}) {
      ChartId c;
      c.kind = Kind::tcone;
      c.side = st.tie_side; c.axis = axis; c.sign = sign;
      c.box = {{{0, st.tie_mu0.ToDouble()}, {0, st.tie_t0.ToDouble()}, {-1, 1}, {-1, 1}, {-1, 1}}};
      charts.push_back(c);
    }
  if (!only.empty()) {
    std::vector<ChartId> keep;
    std::stringstream ss(only);
    std::string name;
    while (std::getline(ss, name, ','))
      for (const ChartId &c : charts) if (c.Name() == name) keep.push_back(c);
    charts = keep;
  }

  std::vector<Stats> stats(charts.size());
  std::vector<std::unique_ptr<Node>> roots(charts.size());
  std::vector<bool> oks(charts.size());
  std::vector<std::vector<std::string>> fails(charts.size());
  const auto start = std::chrono::steady_clock::now();
  std::vector<std::future<void>> futs;
  std::mutex out_mu;
  std::atomic<int> done{0};
  for (int ci = 0; ci < (int)charts.size(); ci++) {
    g_active++;
    futs.push_back(std::async(std::launch::async, [&, ci]() {
      Certifier cert(st, charts[ci], max_depth, &stats[ci]);
      bool ok = false;
      roots[ci] = cert.Rec(charts[ci].box, 0, &ok);
      oks[ci] = ok;
      fails[ci] = cert.fail_boxes;
      g_active--;
      const double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
      std::lock_guard<std::mutex> l(out_mu);
      printf("[%d/%d charts, %.0fs] %-16s %s  leaves %lld  cone %lld  failed %lld  exact-rejected %lld\n", ++done,
             (int)charts.size(), sec, charts[ci].Name().c_str(), ok ? "OK  " : "FAIL", (long long)stats[ci].ok.load(),
             (long long)stats[ci].cone.load(), (long long)stats[ci].failed.load(),
             (long long)stats[ci].exact_fail.load());
      for (const auto &f : fails[ci]) printf("    fail box: %s\n", f.c_str());
    }));
  }
  for (auto &f : futs) f.get();
  int nfail = 0;
  int64_t leaves = 0;
  for (int c = 0; c < (int)charts.size(); c++) {
    if (!oks[c]) nfail++;
    leaves += stats[c].ok;
  }
  printf("%d charts, %d failed, %lld leaves (%s)\n", (int)charts.size(), nfail, (long long)leaves,
         g_double ? "double screen only" : "exact");
  if (!export_file.empty() && nfail == 0 && !g_double) {
    std::string out = "kcapq 1\n";
    for (const auto &v : st.VT) out += "v " + VStr(v) + "\n";
    const char *fn[6] = {"x", "e1", "e2", "Z", "E1", "X"};
    for (int k = 0; k < 6; k++) out += std::string("frame ") + fn[k] + " " + VStr(st.FT[k]) + "\n";
    out += "param " + st.mu0.ToString() + " " + st.R.ToString() + " " + st.t0.ToString() + " " +
           std::to_string(st.tie_side) + " " + st.tie_s0.ToString() + " " + st.tie_t0.ToString() + " " +
           st.tie_mu0.ToString() + "\n";
    for (int c = 0; c < (int)charts.size(); c++) {
      out += "chart " + std::to_string((int)charts[c].kind) + " " + std::to_string(charts[c].side) + " " +
             std::to_string(charts[c].axis) + " " + (charts[c].sign ? "1" : "0") + "\n";
      Serialize(*roots[c], &out);
    }
    out += "end\n";
    FILE *f = fopen(export_file.c_str(), "w");
    CHECK(f != nullptr);
    fwrite(out.data(), 1, out.size(), f);
    fclose(f);
    printf("wrote %s (%zu bytes)\n", export_file.c_str(), out.size());
  }
  return nfail > 0 ? 1 : 0;
}
