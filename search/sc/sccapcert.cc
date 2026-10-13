// sccapcert: exact cap certificates for the snub cube near its zero-margin
// view u* (and a tube around the exact tie that continues from it), for the
// Lean checker Pipeline/KCapCheck.lean. The design and the findings behind it
// are in nopert229/notes/SNUB-CUBE.md (prototype: nopert229/sccap.cc).
//
// The snub cube (model frame of sc_model.cc): the O-orbit of (t, 1, -t^2), t
// the tribonacci constant, in sc_model's slot order. At u* = x/|x|,
// x = (1, 0, t^2) = e_y x p for the vertex p = (-t^2, t, 1), the first-order
// margin vanishes. With the orthogonal frames
//   x = (1, 0, t^2), e1 = (-t^2, 0, 1), e2 = L2 e_y (L2 = twice the slope of
//   the edge-on triangles' circles at x, in Q(t): those circles are the
//   chart lines tau = +-1/2), Z = e_y, E1 = e1 / 4, X = x / 4,
// the charts (Lean: KCapChart) have variables (mu, tau, p0, p1, p2) and
//   view      u = x + mu e (A + tau B), (A, B) = (e1, e2), (-e1, e2), (e2, e1),
//             (-e2, e1) on sides 0..3;
//   rotation  Cayley vector w = mu (s0 Z + s1 E1 + s2 X);
//   fe:    e = 1, s = (p0, p1, p2)                       mu in [0, mu0]
//   face:  e = p0 in [0, 1], s_axis = +-R, the others p1, p2
//   cone:  e = 1, s = (R/2) p0 sigma, sigma on the face (axis, sign) of
//          [-1, 1]^3 (p0 in [0, t0]): the identity
//   tcone: (side 1) tau = t sig_0, s0 = s0* + t sig_1, s1 = t sig_2,
//          s2 = t sig_3 (t = variable 1 in [0, tie_t0], sig on a face of
//          [-1, 1]^4): the exact tie at tau = 0, s = (1, 0, 0) (the rotation
//          about e_y by 2 atan mu maps the view R_y(phi) x to R_y(-phi) x;
//          both widths tie, clearance 0, for mu up to ~0.165). Its mu range
//          is [0, tie_mu0], beyond mu0: a tube around the tie.
// The F_e boxes inside the identity cone (|s|_inf <= t0 R / 2) or (side 1)
// the tie cone (|tau|, |s0 - s0*|, |s1|, |s2| <= tie_t0) are left to the
// cone charts.
//
// A leaf is a balanced witness: contacts k with edge directions
// c_k = v_{b_k} - v_{a_k} (exact; d_k = u x c_k is the exact normal of the
// segment at every view), weights lambda_k (pairs: 1, 1 with c_2 = -c_1;
// triples: the Cramer weights s (c_{k+1} x c_{k+2}) . u), and outer
// candidate sets S_k, every other vertex dominated by S_k[0] on the box. For
// every tuple j of S_0 x S_1 (x S_2), with inner choices i_k (any vertices),
//   P = sum_k lambda_k (N(w) v_{i_k} . d_k - D(w) v_{j_k} . d_k),
//   N(w) v = (1 - |w|^2) v + 2 (w.v) w + 2 w x v, D(w) = 1 + |w|^2,
// divided by the largest power of mu (and t in tie cones, p0 in identity
// cones) dividing it, has a nonnegative tensor Bernstein bound on the box;
// lambda_k >= 0 and sum_k lambda_k |d_k|^2 > 0 on the box. Then
// sum_k lambda_k (R v_{i_k} . d_k - max_j v_j . d_k) >= 0 with a positive
// weight on a nonzero direction: not Rupert (Lean BalancedWitness).
//
// Witnesses are found in double precision; every leaf is then checked
// exactly over Q(t): the polynomials exactly, the divisions exactly (the
// vanishing coefficients must be exactly 0), the bounds by outward-rounded
// interval Bernstein coefficients, and where those are not enough by exact
// Bernstein coefficients bounded by Lean's TribQ.lo (the Lean check).
//
// Usage: sccapcert.exe [--mu0 1/8] [--R 2] [--t0 1/4] [--tie_t0 1/4]
//          [--tie_mu0 1/3] [--max_depth 40] [--threads 64] [--try 16]
//          [--only kind:side:axis:sign,...] [--export FILE] [--caps FILE]
//          [--double]
// --caps writes the main search's cap domains (search5d --trib_caps): the
// cap box (kind 0) and the tie tube (kind 1).

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

namespace {

constexpr int NV = 5;  // chart variables: mu, tau (t), p0, p1, p2
using Exp = std::array<uint8_t, NV>;
using Q = BigRat;
using exact5d::TQ;

int g_try = 16;
bool g_double = false;

// ----- Q(t) -----
TQ TOf(int a) { return {Q(a), Q(0), Q(0)}; }
TQ TOfQ(const Q &a) { return {a, Q(0), Q(0)}; }
TQ operator+(const TQ &x, const TQ &y) { return exact5d::TAdd(x, y); }
TQ operator-(const TQ &x, const TQ &y) { return exact5d::TSub(x, y); }
TQ operator-(const TQ &x) { return {Q(0) - x.a, Q(0) - x.b, Q(0) - x.c}; }
TQ operator*(const TQ &x, const TQ &y) { return exact5d::TMul(x, y); }
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

// ----- Outward-rounded intervals -----
struct Iv { double lo = 0, hi = 0; };
double Dn(double x) { return std::nextafter(x, -INFINITY); }
double Up(double x) { return std::nextafter(x, INFINITY); }
Iv IvOf(double x) { return {x, x}; }
Iv operator+(Iv x, Iv y) {
  if (x.lo == 0 && x.hi == 0) return y;
  if (y.lo == 0 && y.hi == 0) return x;
  return {Dn(x.lo + y.lo), Up(x.hi + y.hi)};
}
Iv operator*(Iv x, Iv y) {
  if ((x.lo == 0 && x.hi == 0) || (y.lo == 0 && y.hi == 0)) return IvOf(0);
  const double p[4] = {x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi};
  return {Dn(*std::min_element(p, p + 4)), Up(*std::max_element(p, p + 4))};
}
Iv kT, kT2;
Iv IvOfQ(const Q &q) {
  if (q == Q(0)) return IvOf(0);
  const double d = q.ToDouble();
  return {Dn(Dn(d)), Up(Up(d))};
}
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

// ----- Polynomials over T (double or TQ) in NV variables -----
template <class T> bool IsZeroT(const T &x) { return IsZero(x); }
template <> bool IsZeroT<double>(const double &x) { return x == 0.0; }
template <class T> T One();
template <> double One<double>() { return 1.0; }
template <> TQ One<TQ>() { return TOf(1); }
template <class T> T FromQ(const Q &q);
template <> double FromQ<double>(const Q &q) { return q.ToDouble(); }
template <> TQ FromQ<TQ>(const Q &q) { return TOfQ(q); }

template <class T>
struct PolyT {
  std::map<Exp, T> t;
  static PolyT Const(const T &c) { PolyT p; if (!IsZeroT(c)) p.t[Exp{}] = c; return p; }
  static PolyT Var(int i) { PolyT p; Exp e{}; e[i] = 1; p.t[e] = One<T>(); return p; }
};
template <class T> PolyT<T> operator+(const PolyT<T> &a, const PolyT<T> &b) {
  PolyT<T> r = a;
  for (const auto &[e, c] : b.t) {
    auto it = r.t.find(e);
    if (it == r.t.end()) r.t[e] = c; else it->second = it->second + c;
  }
  return r;
}
template <class T> PolyT<T> operator-(const PolyT<T> &a, const PolyT<T> &b) {
  PolyT<T> r = a;
  for (const auto &[e, c] : b.t) {
    auto it = r.t.find(e);
    if (it == r.t.end()) r.t[e] = T() - c; else it->second = it->second - c;
  }
  return r;
}
template <class T> PolyT<T> operator*(const PolyT<T> &a, const PolyT<T> &b) {
  PolyT<T> r;
  for (const auto &[ea, ca] : a.t)
    for (const auto &[eb, cb] : b.t) {
      Exp e;
      for (int i = 0; i < NV; i++) e[i] = ea[i] + eb[i];
      auto it = r.t.find(e);
      if (it == r.t.end()) r.t[e] = ca * cb; else it->second = it->second + ca * cb;
    }
  return r;
}
template <class T> PolyT<T> operator*(const T &s, const PolyT<T> &a) {
  PolyT<T> r;
  if (IsZeroT(s)) return r;
  for (const auto &[e, c] : a.t) r.t[e] = s * c;
  return r;
}
template <class T> using V3 = std::array<T, 3>;
template <class T> using PV = std::array<PolyT<T>, 3>;
template <class T> PV<T> PConst(const V3<T> &v) { return {PolyT<T>::Const(v[0]), PolyT<T>::Const(v[1]), PolyT<T>::Const(v[2])}; }
template <class T> PV<T> operator+(const PV<T> &a, const PV<T> &b) { return {a[0] + b[0], a[1] + b[1], a[2] + b[2]}; }
template <class T> PV<T> operator*(const PolyT<T> &s, const PV<T> &a) { return {s * a[0], s * a[1], s * a[2]}; }
template <class T> PolyT<T> PDot(const PV<T> &a, const PV<T> &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
template <class T> PolyT<T> PDot(const PV<T> &a, const V3<T> &c) { return c[0] * a[0] + c[1] * a[1] + c[2] * a[2]; }
template <class T> PV<T> PCross(const PV<T> &a, const PV<T> &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
template <class T> V3<T> VSub(const V3<T> &a, const V3<T> &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
template <class T> V3<T> VCross(const V3<T> &a, const V3<T> &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
template <class T> T VDot(const V3<T> &a, const V3<T> &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }

// p / y_i^m for the largest m dividing p (Lean KPoly.divOut). Double: drops
// |c| <= tol relative to the largest coefficient first (the screen).
double g_div_tol = 1e-11;
PolyT<double> DivideVar(const PolyT<double> &p, int i) {
  double mx = 0;
  for (const auto &[e, c] : p.t) mx = std::max(mx, std::abs(c));
  const double tol = g_div_tol * std::max(1.0, mx);
  int k = 255;
  for (const auto &[e, c] : p.t) if (std::abs(c) > tol) k = std::min<int>(k, e[i]);
  if (k == 255 || k == 0) return p;
  PolyT<double> r;
  for (const auto &[e, c] : p.t) {
    if (std::abs(c) <= tol) continue;
    Exp f = e;
    f[i] -= k;
    r.t[f] = c;
  }
  return r;
}
PolyT<TQ> DivideVar(const PolyT<TQ> &p, int i) {
  int k = 255;
  for (const auto &[e, c] : p.t) if (!IsZero(c)) k = std::min<int>(k, e[i]);
  if (k == 255 || k == 0) return p;
  PolyT<TQ> r;
  for (const auto &[e, c] : p.t) {
    if (IsZero(c)) continue;
    Exp f = e;
    f[i] -= k;
    r.t[f] = c;
  }
  return r;
}

double Eval(const PolyT<double> &p, const double *x) {
  double s = 0;
  for (const auto &[e, c] : p.t) {
    double v = c;
    for (int i = 0; i < NV; i++) for (int k = 0; k < e[i]; k++) v *= x[i];
    s += v;
  }
  return s;
}

// Boxes: [lo, hi] per variable, dyadic rationals (as doubles: exact).
using Box = std::array<std::pair<double, double>, NV>;

// The exact rational value of a double.
Q DyadicRat(double x) {
  if (x == 0) return Q(0);
  int e;
  const double m = std::frexp(x, &e);
  int64_t mi = (int64_t)std::ldexp(m, 53);
  e -= 53;
  while (e < 0 && mi % 2 == 0) { mi /= 2; e++; }
  BigInt p(1);
  for (int i = 0; i < std::abs(e); i++) p = p * BigInt(2);
  return e >= 0 ? Q(BigInt(mi) * p) : Q(BigInt(mi), p);
}

int64_t Binom(int n, int k) {
  int64_t r = 1;
  for (int i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return r;
}

// Tensor Bernstein coefficients (the degrees from the nonzero coefficients,
// as Lean's KPoly.degIn): the Taylor shift x = lo + h y of each variable,
// then the Bernstein conversion. Ops: zero, add, scale by a rational given as
// (numerator, denominator) or by a power product of lo and h.
template <class C, class Ops>
std::vector<C> Bernstein(const std::map<Exp, C> &terms, std::array<int, NV> deg, const std::array<std::pair<Q, Q>, NV> &box,
                         const Ops &ops) {
  std::array<int, NV> sz, stride;
  for (int i = 0; i < NV; i++) sz[i] = deg[i] + 1;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  const int n = stride[0] * sz[0];
  std::vector<C> c(n, ops.zero());
  for (const auto &[e, v] : terms) {
    int idx = 0;
    for (int i = 0; i < NV; i++) idx += e[i] * stride[i];
    c[idx] = ops.add(c[idx], v);
  }
  for (int ax = 0; ax < NV; ax++) {
    const int D = deg[ax];
    if (D == 0) continue;
    const Q &lo = box[ax].first;
    const Q h = box[ax].second - box[ax].first;
    std::vector<C> col(D + 1), out(D + 1);
    for (int base = 0; base < n; base++) {
      if ((base / stride[ax]) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * stride[ax]];
      for (int k = 0; k <= D; k++) out[k] = ops.zero();
      for (int j = 0; j <= D; j++) {
        if (ops.is_zero(col[j])) continue;
        for (int k = 0; k <= j; k++) {
          Q w(Binom(j, k));
          for (int r = 0; r < j - k; r++) w = w * lo;
          for (int r = 0; r < k; r++) w = w * h;
          out[k] = ops.add(out[k], ops.scale(w, col[j]));
        }
      }
      for (int I = 0; I <= D; I++) {
        C s = ops.zero();
        for (int J = 0; J <= I; J++) s = ops.add(s, ops.scale(Q(Binom(I, J), Binom(D, J)), out[J]));
        col[I] = s;
      }
      for (int k = 0; k <= D; k++) c[base + k * stride[ax]] = col[k];
    }
  }
  return c;
}

struct IvOps {
  Iv zero() const { return IvOf(0); }
  Iv add(const Iv &a, const Iv &b) const { return a + b; }
  bool is_zero(const Iv &a) const { return a.lo == 0 && a.hi == 0; }
  Iv scale(const Q &q, const Iv &a) const { return IvOfQ(q) * a; }
};
struct TOps {
  TQ zero() const { return TOf(0); }
  TQ add(const TQ &a, const TQ &b) const { return a + b; }
  bool is_zero(const TQ &a) const { return IsZero(a); }
  TQ scale(const Q &q, const TQ &a) const { return exact5d::TScale(q, a); }
};

std::array<int, NV> Degrees(const PolyT<TQ> &p) {
  std::array<int, NV> deg{};
  for (const auto &[e, c] : p.t)
    if (!IsZero(c)) for (int i = 0; i < NV; i++) deg[i] = std::max<int>(deg[i], e[i]);
  return deg;
}

std::array<std::pair<Q, Q>, NV> BoxQ(const Box &box) {
  std::array<std::pair<Q, Q>, NV> b;
  for (int i = 0; i < NV; i++) b[i] = {DyadicRat(box[i].first), DyadicRat(box[i].second)};
  return b;
}

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

// Double Bernstein lower bound (the screen).
double BernsteinLowerD(const PolyT<double> &p, const Box &box) {
  std::array<int, NV> deg{};
  for (const auto &[e, c] : p.t) if (c != 0) for (int i = 0; i < NV; i++) deg[i] = std::max<int>(deg[i], e[i]);
  std::array<int, NV> sz, stride;
  for (int i = 0; i < NV; i++) sz[i] = deg[i] + 1;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  const int n = stride[0] * sz[0];
  std::vector<double> c(n, 0.0);
  for (const auto &[e, v] : p.t) {
    int idx = 0;
    for (int i = 0; i < NV; i++) idx += e[i] * stride[i];
    c[idx] += v;
  }
  for (int ax = 0; ax < NV; ax++) {
    const int D = deg[ax];
    if (D == 0) continue;
    const double lo = box[ax].first, h = box[ax].second - box[ax].first;
    std::vector<double> col(D + 1), out(D + 1);
    for (int base = 0; base < n; base++) {
      if ((base / stride[ax]) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * stride[ax]];
      std::fill(out.begin(), out.end(), 0.0);
      for (int j = 0; j <= D; j++) {
        if (col[j] == 0) continue;
        for (int k = 0; k <= j; k++) out[k] += col[j] * (double)Binom(j, k) * std::pow(lo, j - k) * std::pow(h, k);
      }
      for (int I = 0; I <= D; I++) {
        double s = 0;
        for (int J = 0; J <= I; J++) s += (double)Binom(I, J) / (double)Binom(D, J) * out[J];
        col[I] = s;
      }
      for (int k = 0; k <= D; k++) c[base + k * stride[ax]] = col[k];
    }
  }
  double m = INFINITY;
  for (double x : c) m = std::min(m, x);
  return m;
}

// ----- The solid and the frame -----
struct Setup {
  std::vector<V3<TQ>> VT;
  std::vector<V3<double>> V;
  // x, e1, e2, Z, E1, X.
  std::array<V3<TQ>, 6> FT;
  std::array<V3<double>, 6> F;
  TQ L2;
  Q mu0{1, 8}, R{2}, t0{1, 4}, tie_s0{1}, tie_t0{1, 4}, tie_mu0{1, 3};
  int tie_side = 1;
};

V3<double> ToD(const V3<TQ> &v) { return {TD(v[0]), TD(v[1]), TD(v[2])}; }

using M3 = std::array<std::array<int, 3>, 3>;
std::vector<M3> Octahedral() {
  std::vector<M3> G;
  const int perms[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};
  const int psign[6] = {1, -1, -1, 1, 1, -1};
  for (int p = 0; p < 6; p++)
    for (int s = 0; s < 8; s++) {
      const int sg[3] = {s & 1 ? -1 : 1, s & 2 ? -1 : 1, s & 4 ? -1 : 1};
      if (psign[p] * sg[0] * sg[1] * sg[2] != 1) continue;
      M3 m{};
      for (int r = 0; r < 3; r++) m[r][perms[p][r]] = sg[r];
      G.push_back(m);
    }
  CHECK(G.size() == 24);
  return G;
}
M3 Mul(const M3 &a, const M3 &b) {
  M3 r{};
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++)
      for (int k = 0; k < 3; k++) r[i][j] += a[i][k] * b[k][j];
  return r;
}
V3<TQ> Apply(const M3 &m, const V3<TQ> &v) {
  V3<TQ> r;
  for (int i = 0; i < 3; i++) {
    r[i] = TOf(0);
    for (int j = 0; j < 3; j++) r[i] = r[i] + exact5d::TScale(Q(m[i][j]), v[j]);
  }
  return r;
}

void MakeSolid(Setup *st) {
  // sc_model.cc's slot order: vertex 6 k + s = Rz(pi/2)^k seed_s, the seeds
  // the images of (t, 1, -t^2) under the coset representatives of O / C4,
  // sorted by decreasing z, then y.
  const TQ t{Q(0), Q(1), Q(0)}, t2{Q(0), Q(0), Q(1)};
  const V3<TQ> seed{t, TOf(1), -t2};
  const std::vector<M3> G = Octahedral();
  const M3 rz{{{0, -1, 0}, {1, 0, 0}, {0, 0, 1}}};
  M3 rzk[4];
  rzk[0] = {{{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}};
  for (int k = 1; k < 4; k++) rzk[k] = Mul(rz, rzk[k - 1]);
  std::vector<M3> reps;
  for (const M3 &g : G) {
    bool seen = false;
    for (const M3 &h : reps)
      for (int k = 0; k < 4; k++) seen = seen || Mul(rzk[k], h) == g;
    if (!seen) reps.push_back(g);
  }
  CHECK(reps.size() == 6);
  std::sort(reps.begin(), reps.end(), [&](const M3 &a, const M3 &b) {
    const V3<TQ> pa = Apply(a, seed), pb = Apply(b, seed);
    if (std::abs(TD(pa[2]) - TD(pb[2])) > 1e-9) return TD(pb[2]) < TD(pa[2]);
    return TD(pb[1]) < TD(pa[1]);
  });
  for (int k = 0; k < 4; k++)
    for (int s = 0; s < 6; s++) {
      st->VT.push_back(Apply(Mul(rzk[k], reps[s]), seed));
      st->V.push_back(ToD(st->VT.back()));
    }
  // The frame.
  const V3<TQ> x{TOf(1), TOf(0), t2}, e1{-t2, TOf(0), TOf(1)};
  // L2: the edge-on triangles at x (faces through three vertices, every
  // vertex on one side, normal n with n . x = 0); the tangent n x x of the
  // circle of views keeping one edge-on is a e1 + b e_y: L2 = 2 max |b / a|.
  TQ L2 = TOf(0);
  double best = 0;
  const int n = st->VT.size();
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++)
      for (int c = b + 1; c < n; c++) {
        const V3<TQ> nf = VCross(VSub(st->VT[b], st->VT[a]), VSub(st->VT[c], st->VT[a]));
        if (IsZero(nf[0]) && IsZero(nf[1]) && IsZero(nf[2])) continue;
        bool pos = false, neg = false;
        int on = 0;
        for (int j = 0; j < n; j++) {
          const TQ d = VDot(nf, VSub(st->VT[j], st->VT[a]));
          if (IsZero(d)) on++;
          else (TD(d) > 0 ? pos : neg) = true;
        }
        if ((pos && neg) || on != 3) continue;
        if (!IsZero(VDot(nf, x))) continue;
        const V3<TQ> tang = VCross(nf, x);
        // a = tang . e1 / |e1|^2, b = tang_y.
        const TQ ta = VDot(tang, e1) * TInv(VDot(e1, e1)), tb = tang[1];
        TQ r = tb * TInv(ta);
        if (TD(r) < 0) r = -r;
        if (TD(r) > best) { best = TD(r); L2 = r + r; }
      }
  CHECK(best > 0);
  st->L2 = L2;
  const Q quarter(1, 4);
  st->FT = {x, e1, V3<TQ>{TOf(0), L2, TOf(0)}, V3<TQ>{TOf(0), TOf(1), TOf(0)},
            V3<TQ>{exact5d::TScale(quarter, e1[0]), TOf(0), exact5d::TScale(quarter, e1[2])},
            V3<TQ>{exact5d::TScale(quarter, x[0]), TOf(0), exact5d::TScale(quarter, x[2])}};
  for (int f = 0; f < 6; f++) st->F[f] = ToD(st->FT[f]);
  printf("L2 = %s + %s t + %s t^2 = %.12f\n", L2.a.ToString().c_str(), L2.b.ToString().c_str(),
         L2.c.ToString().c_str(), TD(L2));
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
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      CHECK(i + 1 < argc) << a;
      return argv[++i];
    };
    if (a == "--mu0") st.mu0 = ParseQ(next());
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
  MakeSolid(&st);

  if (!caps_file.empty()) {
    FILE *f = fopen(caps_file.c_str(), "w");
    CHECK(f != nullptr);
    std::string frame;
    for (int k = 0; k < 6; k++) frame += " " + VStr(st.FT[k]);
    fprintf(f, "# sccapcert: kind mu0 R t0 s0, then x e1 e2 Z E1 X (a b c = a + b t + c t^2)\n");
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
    std::string out = "sccapcert 1\n";
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
