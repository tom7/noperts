// Polynomials in five chart variables over an exact scalar (or double), and
// their tensor Bernstein bounds on boxes: the C++ side of Lean's
// Pipeline/KPoly.lean, shared by the cap certificate generators
// (search/sc/sccapcert.cc over Q(t), search/common/idcap.cc over Q).
//
// A scalar type T needs, in namespace kpoly: IsZeroT<T>, One<T>, FromQ<T>
// (double's are here), and +, -, * (unary minus via T() - x).

#ifndef _NOPERT_KPOLY_H
#define _NOPERT_KPOLY_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <map>
#include <utility>
#include <vector>

#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace kpoly {

constexpr int NV = 5;  // chart variables
using Exp = std::array<uint8_t, NV>;
using Q = BigRat;

// ----- Outward-rounded intervals -----
struct Iv { double lo = 0, hi = 0; };
inline double Dn(double x) { return std::nextafter(x, -INFINITY); }
inline double Up(double x) { return std::nextafter(x, INFINITY); }
inline Iv IvOf(double x) { return {x, x}; }
inline Iv operator+(Iv x, Iv y) {
  if (x.lo == 0 && x.hi == 0) return y;
  if (y.lo == 0 && y.hi == 0) return x;
  return {Dn(x.lo + y.lo), Up(x.hi + y.hi)};
}
inline Iv operator*(Iv x, Iv y) {
  if ((x.lo == 0 && x.hi == 0) || (y.lo == 0 && y.hi == 0)) return IvOf(0);
  const double p[4] = {x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi};
  return {Dn(*std::min_element(p, p + 4)), Up(*std::max_element(p, p + 4))};
}
inline Iv IvOfQ(const Q &q) {
  if (q == Q(0)) return IvOf(0);
  const double d = q.ToDouble();
  return {Dn(Dn(d)), Up(Up(d))};
}

// ----- Scalars -----
template <class T> bool IsZeroT(const T &x);
template <> inline bool IsZeroT<double>(const double &x) { return x == 0.0; }
template <class T> T One();
template <> inline double One<double>() { return 1.0; }
template <class T> T FromQ(const Q &q);
template <> inline double FromQ<double>(const Q &q) { return q.ToDouble(); }

// ----- Polynomials over T in NV variables -----
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
inline double g_div_tol = 1e-11;
inline PolyT<double> DivideVar(const PolyT<double> &p, int i) {
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
// The exact division: the vanishing coefficients must be exactly zero.
template <class T> PolyT<T> DivideVar(const PolyT<T> &p, int i) {
  int k = 255;
  for (const auto &[e, c] : p.t) if (!IsZeroT(c)) k = std::min<int>(k, e[i]);
  if (k == 255 || k == 0) return p;
  PolyT<T> r;
  for (const auto &[e, c] : p.t) {
    if (IsZeroT(c)) continue;
    Exp f = e;
    f[i] -= k;
    r.t[f] = c;
  }
  return r;
}

inline double Eval(const PolyT<double> &p, const double *x) {
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
inline Q DyadicRat(double x) {
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

inline int64_t Binom(int n, int k) {
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

template <class T> std::array<int, NV> Degrees(const PolyT<T> &p) {
  std::array<int, NV> deg{};
  for (const auto &[e, c] : p.t)
    if (!IsZeroT(c)) for (int i = 0; i < NV; i++) deg[i] = std::max<int>(deg[i], e[i]);
  return deg;
}

inline std::array<std::pair<Q, Q>, NV> BoxQ(const Box &box) {
  std::array<std::pair<Q, Q>, NV> b;
  for (int i = 0; i < NV; i++) b[i] = {DyadicRat(box[i].first), DyadicRat(box[i].second)};
  return b;
}

// Double Bernstein lower bound (the screen).
inline double BernsteinLowerD(const PolyT<double> &p, const Box &box) {
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

}  // namespace kpoly

#endif
