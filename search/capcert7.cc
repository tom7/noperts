// capcert7: the cap certificate for the 7-vertex C3v candidate (nopert_233,
// nopert233_model.txt) at its mirror normal, after capcert.cc (the deltoidal
// hexecontahedron's caps; this is its u0 case). Near the mirror normal x the
// identity's first-order cage degenerates and the mirror tie H_u Q (Q = H_x,
// -Q the mirror) approaches the identity, so the poses (view u = x + mu e a,
// Cayley rotation w) are blown up in weighted coordinates
//   w = mu (s1 e1 + s2 e2) + mu^2 s3 x
// with charts on the faces of the weighted cube max(e, |s|/2) = 1 and a cone
// chart at the identity. The frame is rational and unnormalized:
// x = (1,0,-1) (the normal of the mirror swapping the first and third
// coordinates), e1 = (0,1,0), e2 = (1,0,1); everything is homogeneous in u,
// and the frame's scale only rescales the chart coordinates.
//
// The solid is not centrally symmetric, so each box is certified by a
// two-sided width witness (vertices k, k', direction c), d = u x c:
//   P_{j,j'} = (N(w) (v_k - v_k') - D(w) (v_j - v_j')) . d >= 0 for all j, j'
// (each divided by the largest powers of mu and of the cone radius t that
// divide it): then the inner shadow is at least as wide as the outer one in
// the direction d, so the pose is not a passage, whatever the offset
// (Lean: Nopert7/WidthWitness.lean). Boxes outside the mirror-tie cell
// (tr(H_u R Q) > tr R) are pruned.
//
// Witnesses are screened in double precision; the exact mode computes over
// Q (the KNum field's rational part; the solid and frame are rational) with
// outward-rounded Bernstein bounds. --double: feasibility only.
//
// Usage: capcert7.exe [--model nopert233_model.txt] [--mu0 1/64] [--max_depth 30]
//          [--threads 60] [--try 24] [--only kind:side:axis:sign,...] [--double]
//          [--strong_scale S] [--ratio_z Z] [--export FILE]

#include <algorithm>
#include <array>
#include <atomic>
#include <cfenv>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <map>
#include <set>
#include <memory>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"

namespace {


constexpr int NV = 5;  // variables: mu, tau, p1, p2, p3
int g_try = 24;
using Exp = std::array<uint8_t, NV>;
using Q = BigRat;

// ----- The field K = Q(sqrt5, s), s^2 = (5 + sqrt5)/8 -----
struct KNum {
  Q a{0}, b{0}, c{0}, d{0};
  KNum() = default;
  explicit KNum(int v) : a(v) {}
  KNum(Q a_, Q b_, Q c_, Q d_) : a(a_), b(b_), c(c_), d(d_) {}
};
KNum operator+(const KNum &x, const KNum &y) { return {x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d}; }
KNum operator-(const KNum &x, const KNum &y) { return {x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d}; }
KNum operator-(const KNum &x) { return {-x.a, -x.b, -x.c, -x.d}; }
KNum operator*(const KNum &x, const KNum &y) {
  const Q p = x.c * y.c + Q(5) * x.d * y.d, q = x.c * y.d + x.d * y.c;
  return {x.a * y.a + Q(5) * x.b * y.b + (Q(5) * p + Q(5) * q) / Q(8),
          x.a * y.b + x.b * y.a + (p + Q(5) * q) / Q(8),
          x.a * y.c + Q(5) * x.b * y.d + x.c * y.a + Q(5) * x.d * y.b,
          x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a};
}
bool IsZero(const KNum &x) { return x.a == Q(0) && x.b == Q(0) && x.c == Q(0) && x.d == Q(0); }
KNum Inv(const KNum &x) {
  // 1/x: (A + B s)(A - B s) = A^2 - B^2 s^2 in Q(sqrt5), A = a + b sqrt5, B = c + d sqrt5.
  const KNum A{x.a, x.b, Q(0), Q(0)}, B{x.c, x.d, Q(0), Q(0)}, S{Q(0), Q(0), Q(1), Q(0)};
  const KNum s2{Q(5, 8), Q(1, 8), Q(0), Q(0)};
  const KNum n = A * A - B * B * s2;
  CHECK(n.c == Q(0) && n.d == Q(0));
  const Q den = n.a * n.a - Q(5) * n.b * n.b;
  const KNum ninv{n.a / den, -n.b / den, Q(0), Q(0)};
  return (A - B * S) * ninv;
}

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
Iv kSqrt5, kS;
Iv IvOfQ(const Q &q) {
  if (q == Q(0)) return IvOf(0);
  const double d = q.ToDouble();
  return {Dn(Dn(d)), Up(Up(d))};
}
void InitConstants() {
  const Q r5lo("2236067977499789/1000000000000000"), r5hi("2236067977499790/1000000000000000");
  CHECK(r5lo * r5lo < Q(5) && Q(5) < r5hi * r5hi);
  kSqrt5 = {Dn(r5lo.ToDouble()), Up(r5hi.ToDouble())};
  const Q slo("951056516295153/1000000000000000"), shi("951056516295154/1000000000000000");
  CHECK(slo * slo < (Q(5) + r5lo) / Q(8) && (Q(5) + r5hi) / Q(8) < shi * shi);
  kS = {Dn(slo.ToDouble()), Up(shi.ToDouble())};
}
Iv IvOfK(const KNum &x) {
  if (IsZero(x)) return IvOf(0);
  return IvOfQ(x.a) + IvOfQ(x.b) * kSqrt5 + IvOfQ(x.c) * kS + IvOfQ(x.d) * (kSqrt5 * kS);
}
double ToDouble(const KNum &x) { const Iv v = IvOfK(x); return 0.5 * (v.lo + v.hi); }

// ----- Polynomials over T (double or KNum) in NV variables -----
template <class T> T Zero() { return T(0); }
template <> double Zero<double>() { return 0.0; }
template <class T> bool IsZeroT(const T &x) { return IsZero(x); }
template <> bool IsZeroT<double>(const double &x) { return x == 0.0; }

template <class T>
struct PolyT {
  std::map<Exp, T> t;
  static PolyT Const(const T &c) { PolyT p; if (!IsZeroT(c)) p.t[Exp{}] = c; return p; }
  static PolyT Var(int i) { PolyT p; Exp e{}; e[i] = 1; p.t[e] = T(1); return p; }
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
    if (it == r.t.end()) r.t[e] = Zero<T>() - c; else it->second = it->second - c;
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
  for (const auto &[e, c] : a.t) r.t[e] = s * c;
  return r;
}
template <class T> using V3 = std::array<T, 3>;
// An integer-valued double as T (the chart ranges are integers).
template <class T> T ScaleT(double v) { CHECK(v == std::round(v)) << v; return T((int)v); }
template <> double ScaleT<double>(double v) { return v; }
template <class T> using PVecT = std::array<PolyT<T>, 3>;
template <class T> PVecT<T> PConst(const V3<T> &v) {
  return {PolyT<T>::Const(v[0]), PolyT<T>::Const(v[1]), PolyT<T>::Const(v[2])};
}
template <class T> PVecT<T> operator+(const PVecT<T> &a, const PVecT<T> &b) { return {a[0] + b[0], a[1] + b[1], a[2] + b[2]}; }
template <class T> PVecT<T> operator*(const PolyT<T> &s, const PVecT<T> &a) { return {s * a[0], s * a[1], s * a[2]}; }
template <class T> PVecT<T> operator*(const T &s, const PVecT<T> &a) { return {s * a[0], s * a[1], s * a[2]}; }
template <class T> PolyT<T> PDot(const PVecT<T> &a, const PVecT<T> &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
template <class T> PolyT<T> PDot(const PVecT<T> &a, const V3<T> &c) { return c[0] * a[0] + c[1] * a[1] + c[2] * a[2]; }
template <class T> PVecT<T> PCross(const PVecT<T> &a, const PVecT<T> &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
template <class T> V3<T> VCross(const V3<T> &a, const V3<T> &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
template <class T> T VDot(const V3<T> &a, const V3<T> &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
template <class T> V3<T> VSub(const V3<T> &a, const V3<T> &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
template <class T> V3<T> VScale(const T &s, const V3<T> &a) { return {s * a[0], s * a[1], s * a[2]}; }

// Divide by the largest power of variable i dividing p. Double: drop |c| <= tol
// first; exact: only exact zeros vanish.
PolyT<double> DivideVar(const PolyT<double> &p, int i, double tol = 1e-12) {
  PolyT<double> q;
  int m = 1000;
  for (const auto &[e, c] : p.t) if (std::abs(c) > tol) m = std::min(m, (int)e[i]);
  if (m == 1000) return q;
  for (const auto &[e, c] : p.t) {
    if (std::abs(c) <= tol) continue;
    Exp f = e;
    f[i] -= m;
    q.t[f] = c;
  }
  return q;
}
PolyT<KNum> DivideVar(const PolyT<KNum> &p, int i) {
  PolyT<KNum> q;
  int m = 1000;
  for (const auto &[e, c] : p.t) if (!IsZero(c)) m = std::min(m, (int)e[i]);
  if (m == 1000) return q;
  for (const auto &[e, c] : p.t) {
    if (IsZero(c)) continue;
    Exp f = e;
    f[i] -= m;
    q.t[f] = c;
  }
  return q;
}

double EvalD(const PolyT<double> &p, const double *x) {
  double s = 0;
  for (const auto &[e, c] : p.t) {
    double v = c;
    for (int i = 0; i < NV; i++) for (int k = 0; k < e[i]; k++) v *= x[i];
    s += v;
  }
  return s;
}

// Dense tensor of interval coefficients.
struct Dense {
  std::array<int, NV> deg{};
  std::vector<Iv> c;
  int Index(const Exp &e) const {
    int idx = 0;
    for (int i = 0; i < NV; i++) idx = idx * (deg[i] + 1) + e[i];
    return idx;
  }
};
template <class T> Iv ToIv(const T &x);
template <> Iv ToIv<double>(const double &x) { return IvOf(x); }  // double mode: not rigorous
template <> Iv ToIv<KNum>(const KNum &x) { return IvOfK(x); }
template <class T> Dense ToDense(const PolyT<T> &p) {
  // Degrees from the nonzero coefficients only (cancelled terms stay in the map),
  // so that the Lean checker (NPoly.degIn) uses the same Bernstein degrees.
  Dense d;
  for (const auto &[e, c] : p.t)
    if (!IsZeroT(c)) for (int i = 0; i < NV; i++) d.deg[i] = std::max(d.deg[i], (int)e[i]);
  int n = 1;
  for (int i = 0; i < NV; i++) n *= d.deg[i] + 1;
  d.c.assign(n, IvOf(0));
  for (const auto &[e, c] : p.t)
    if (!IsZeroT(c)) d.c[d.Index(e)] = d.c[d.Index(e)] + ToIv(c);
  return d;
}

double Binom(int n, int k) {
  double r = 1;
  for (int i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return r;  // exact for the small n here
}

using Box = std::array<std::pair<double, double>, NV>;

// Lower bound by tensor Bernstein coefficients (interval arithmetic; box
// endpoints are dyadic, so lo and h are exact).
double BernsteinLower(const Dense &d, const Box &box) {
  std::vector<Iv> c = d.c;
  std::array<int, NV> sz, stride;
  for (int i = 0; i < NV; i++) sz[i] = d.deg[i] + 1;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  const int n = c.size();
  for (int ax = 0; ax < NV; ax++) {
    const int D = d.deg[ax];
    if (D == 0) continue;
    const double lo = box[ax].first, h = box[ax].second - box[ax].first;
    std::vector<Iv> col(D + 1), out(D + 1);
    for (int base = 0; base < n; base++) {
      if ((base / stride[ax]) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * stride[ax]];
      for (int k = 0; k <= D; k++) out[k] = IvOf(0);
      for (int j = 0; j <= D; j++) {
        if (col[j].lo == 0 && col[j].hi == 0) continue;
        for (int k = 0; k <= j; k++) {
          // C(j,k) lo^(j-k) h^k (exact powers of dyadics, small exponents)
          Iv w = IvOf(Binom(j, k));
          for (int r = 0; r < j - k; r++) w = w * IvOf(lo);
          for (int r = 0; r < k; r++) w = w * IvOf(h);
          out[k] = out[k] + col[j] * w;
        }
      }
      for (int I = 0; I <= D; I++) {
        Iv s = IvOf(0);
        for (int J = 0; J <= I; J++) {
          // C(I,J)/C(D,J): rational; enclose it.
          const double num = Binom(I, J), den = Binom(D, J);
          const Iv q = {Dn(num / den), Up(num / den)};
          s = s + q * out[J];
        }
        col[I] = s;
      }
      for (int k = 0; k <= D; k++) c[base + k * stride[ax]] = col[k];
    }
  }
  double m = INFINITY;
  for (const Iv &x : c) m = std::min(m, x.lo);
  return m;
}

// The exact rational value of a double (all box endpoints are dyadic).
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
std::string DyadicQ(double x) {
  if (x == 0) return "0";
  int e;
  const double m = std::frexp(x, &e);
  int64_t mi = (int64_t)std::ldexp(m, 53);
  e -= 53;
  while (e < 0 && mi % 2 == 0) { mi /= 2; e++; }
  BigInt p(1);
  for (int i = 0; i < std::abs(e); i++) p = p * BigInt(2);
  return (e >= 0 ? Q(BigInt(mi) * p) : Q(BigInt(mi), p)).ToString();
}

// Exact tensor Bernstein lower bound (the fallback when the interval bound is
// slightly negative because a coefficient vanishes only by cancellation): the
// coefficients are computed exactly in K and bounded below by the rational
// enclosure of Lean's IcoQ.lo — the same test as the Lean checker
// (NPoly.lowerDeg at the same uniform degrees).
struct DenseK {
  std::array<int, NV> deg{};
  std::vector<KNum> c;
};
DenseK ToDenseK(const PolyT<KNum> &p) {
  DenseK d;
  for (const auto &[e, c] : p.t)
    if (!IsZero(c)) for (int i = 0; i < NV; i++) d.deg[i] = std::max(d.deg[i], (int)e[i]);
  int n = 1;
  for (int i = 0; i < NV; i++) n *= d.deg[i] + 1;
  d.c.assign(n, KNum(0));
  for (const auto &[e, c] : p.t) {
    if (IsZero(c)) continue;
    int idx = 0;
    for (int i = 0; i < NV; i++) idx = idx * (d.deg[i] + 1) + e[i];
    d.c[idx] = d.c[idx] + c;
  }
  return d;
}
KNum ScaleK(const Q &q, const KNum &x) { return {q * x.a, q * x.b, q * x.c, q * x.d}; }
Q ExactBernsteinLower(const DenseK &d, const std::array<std::pair<Q, Q>, NV> &box) {
  std::vector<KNum> c = d.c;
  std::array<int, NV> sz, stride;
  for (int i = 0; i < NV; i++) sz[i] = d.deg[i] + 1;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  const int n = c.size();
  for (int ax = 0; ax < NV; ax++) {
    const int D = d.deg[ax];
    if (D == 0) continue;
    const Q lo = box[ax].first, h = box[ax].second - box[ax].first;
    std::vector<KNum> col(D + 1), out(D + 1);
    for (int base = 0; base < n; base++) {
      if ((base / stride[ax]) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * stride[ax]];
      for (int k = 0; k <= D; k++) out[k] = KNum(0);
      for (int j = 0; j <= D; j++) {
        if (IsZero(col[j])) continue;
        for (int k = 0; k <= j; k++) {
          Q w((int64_t)std::llround(Binom(j, k)));
          for (int r = 0; r < j - k; r++) w = w * lo;
          for (int r = 0; r < k; r++) w = w * h;
          out[k] = out[k] + ScaleK(w, col[j]);
        }
      }
      for (int I = 0; I <= D; I++) {
        KNum s(0);
        for (int J = 0; J <= I; J++)
          s = s + ScaleK(Q((int64_t)std::llround(Binom(I, J))) / Q((int64_t)std::llround(Binom(D, J))), out[J]);
        col[I] = s;
      }
      for (int k = 0; k <= D; k++) c[base + k * stride[ax]] = col[k];
    }
  }
  bool first = true;
  Q m(0);
  for (const KNum &x : c) {
    const Q l = exact5d::KLower(exact5d::KQ{x.a, x.b, x.c, x.d});
    if (first || l < m) { m = l; first = false; }
  }
  return m;
}

// ----- The solid, the frame, the witnesses -----
template <class T>
struct Problem {
  std::vector<V3<T>> V;
  V3<T> x, e1, e2;
  struct Witness { int k, kp; V3<T> c; };
  std::vector<Witness> W;
};

struct Setup {
  Problem<double> pd;
  Problem<KNum> pk;
  std::vector<std::pair<int, int>> edges;
  bool half_turn = false, tie_cones = false, aniso = false;
  double mu0 = 41.0 / 512, t0 = 0.25;
  double t0m = 0.25;  // the tie cone's radius (--t0_mcone; larger covers the tie line further out)
  int mcm = 1;  // the tie cone's strong-coordinate scale multiplier (--mcone_strong_mul)
  double ConeScale(const std::string &kind, int i) const { return Range(i) / 2 * (kind == "Mcone" && Strong(i) ? mcm : 1); }
  // Strong (weight-2) coordinates range over [-S, S] (S = strong_scale) instead of
  // [-2, 2], so that mu0 ~ 0.01 covers strong components up to S mu0^2.
  double strong_scale = 2;
  bool Strong(int i) const { return aniso ? i >= 1 : i == 2; }
  int ratio_z = 0;       // Z for the ratio blow-up (0: off): Fe and cone charts
  int ratio_z_face = 0;  // Z for face charts (0: ratio_z)
  int tie_ratio = 0;     // Z2 for the tie-centred side-2 strong-face charts (0: off)
  std::set<std::string> tie_charts;  // base charts using the tie scheme (kind:side:axis:sign)
  int tie_k = 0, tie_kp = 0;         // K, K' (0: Z + Z2 + 8, K + 16)
  int TieK(int z) const { return tie_k > 0 ? tie_k : z + tie_ratio + 8; }
  int TieKp(int z) const { return tie_kp > 0 ? tie_kp : TieK(z) + 16; }
  // --z_override kind:side:axis:sign=Z,... (per base chart; e.g. the two ux strong faces need 1024).
  std::map<std::string, int> z_override;
  int Z(const std::string &kind, int side, int axis, double sign) const {
    const auto it = z_override.find(kind + ":" + std::to_string(side) + ":" + std::to_string(axis) + ":" +
                                    (sign > 0 ? "1" : "-1"));
    if (it != z_override.end()) return it->second;
    return kind == "face" && ratio_z_face > 0 ? ratio_z_face : ratio_z;
  }
  double Range(int i) const { return Strong(i) ? strong_scale : 2.0; }
};

KNum ParseKTok(std::istringstream &ss) {
  std::string t[4];
  for (auto &s : t) CHECK(ss >> s);
  return {Q(std::string_view(t[0])), Q(std::string_view(t[1])), Q(std::string_view(t[2])), Q(std::string_view(t[3]))};
}

std::string g_model = "nopert233_model.txt";

void LoadSolid(Setup *s) {
  // Exact rational vertices and the faces from the model file (c3v_model.py).
  std::ifstream in(g_model);
  CHECK(in.good()) << g_model;
  std::string line;
  std::vector<std::vector<int>> faces;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    if (tag == "rational_vertex") {
      int i;
      ss >> i;
      CHECK(i == (int)s->pk.V.size());
      V3<KNum> v;
      for (int a = 0; a < 3; a++) {
        std::string t;
        CHECK(ss >> t);
        v[a] = KNum{Q(std::string_view(t)), Q(0), Q(0), Q(0)};
      }
      s->pk.V.push_back(v);
    } else if (tag == "face") {
      std::vector<int> f;
      int k;
      while (ss >> k) f.push_back(k);
      faces.push_back(f);
    }
  }
  for (const auto &v : s->pk.V) s->pd.V.push_back({ToDouble(v[0]), ToDouble(v[1]), ToDouble(v[2])});
  for (const auto &f : faces)
    for (size_t k = 0; k < f.size(); k++) {
      const auto e = std::minmax(f[k], f[(k + 1) % f.size()]);
      if (std::find(s->edges.begin(), s->edges.end(), std::pair<int, int>(e.first, e.second)) == s->edges.end())
        s->edges.push_back({e.first, e.second});
    }
  CHECK(s->pk.V.size() == 7 && s->edges.size() == 15) << s->pk.V.size() << " " << s->edges.size();
}

std::vector<int> SupportVertices(const std::vector<V3<double>> &V, const V3<double> &u) {
  auto nrm = [](V3<double> a) { const double n = std::sqrt(VDot(a, a)); return V3<double>{a[0] / n, a[1] / n, a[2] / n}; };
  const V3<double> a = nrm(VCross(u, V3<double>{0, 0, 1})), b = VCross(u, a);
  const int n = V.size();
  std::vector<std::array<double, 2>> P(n);
  for (int i = 0; i < n; i++) P[i] = {VDot(V[i], a), VDot(V[i], b)};
  std::vector<int> idx(n);
  for (int i = 0; i < n; i++) idx[i] = i;
  std::sort(idx.begin(), idx.end(), [&](int x, int y) { return P[x] < P[y]; });
  auto cr = [&](int o, int p, int q) {
    return (P[p][0] - P[o][0]) * (P[q][1] - P[o][1]) - (P[p][1] - P[o][1]) * (P[q][0] - P[o][0]);
  };
  std::vector<int> H;
  for (int pass = 0; pass < 2; pass++) {
    const size_t start = H.size();
    for (int i : idx) {
      while (H.size() >= start + 2 && cr(H[H.size() - 2], H.back(), i) <= 0) H.pop_back();
      H.push_back(i);
    }
    H.pop_back();
    std::reverse(idx.begin(), idx.end());
  }
  std::vector<int> out;
  for (int i = 0; i < n; i++) {
    bool on = false;
    for (size_t k = 0; k < H.size() && !on; k++) {
      const int p0 = H[k], p1 = H[(k + 1) % H.size()];
      const double L = std::hypot(P[p1][0] - P[p0][0], P[p1][1] - P[p0][1]);
      on = (i == p0) || (L > 0 && std::abs(cr(p0, p1, i)) / L < 1e-9);
    }
    if (on) out.push_back(i);
  }
  return out;
}

// ----- Charts -----
struct ChartId {
  std::string kind;  // Fe, cone, Mcone, face
  int side = 0, axis = 0;
  double sign = 1;
  Box box;
  // Ratio blow-up of the weak coordinates (charts dominated by a strong one):
  // 0 none; 1 inner: every weak coordinate's variable v becomes mu v (v in
  // [-Z, Z]); 2 outer: weak coordinate `ratio_coord` becomes ratio_sign (Z mu + v)
  // (v in [0, range]).
  // Tie-centred modes (side-2 strong faces, --tie_ratio Z2; they replace ratio 2 on
  // weak coordinate 0 with sign +, i.e. s0 >= Z mu): the tie locus is s0 = e.
  //   3 (band): e = (Z - Z2) mu + p0, s0 = e + mu p1, p1 in [-Z2, Z2];
  //   4 (beyond, e large): e = (Z - Z2) mu + p0, s0 = e + Z2 mu + p1, p1 in [0, 2];
  //   6 (beyond, e small): e = mu p0, p0 in [0, Z - Z2], s0 = Z mu + p1, p1 in [0, 2];
  //   5 (between): e = (Z + Z2) mu + p0, s0 = Z mu + p1 p0, p1 in [0, 1].
  // Tie scheme (--tie_charts; replaces all ratio charts of the listed side-2
  // strong-face base charts; s0 is the weak coordinate, e the view offset; K >=
  // Z + Z2, K' > K):
  //   10: e = mu p0 (p0 in [0, K]), s0 = mu p1 (p1 in [-K', K'])
  //   11/12: e = mu p0, s0 = +-(K' mu + p1) (p1 in [0, 2])
  //   13: e = K mu + p0 (p0 in [0, 1]), s0 = mu p1 (p1 in [-Z, Z])
  //   14: e = K mu + p0, s0 = -(Z mu + p1) (p1 in [0, 2])
  //   15: e = K mu + p0, s0 = e + mu p1 (p1 in [-Z2, Z2])
  //   16: e = K mu + p0, s0 = e + Z2 mu + p1 (p1 in [0, 2])
  //   17: e = K mu + p0, s0 = Z mu + p1 (p0 + (K - Z - Z2) mu) (p1 in [0, 1])
  int ratio = 0, ratio_coord = 0;
  double ratio_sign = 1;
};

template <class T>
struct ChartT {
  PVecT<T> u, w;
  PolyT<T> cell;  // half-turn cell polynomial (prune if > 0)
};

template <class T>
ChartT<T> MakeChart(const Setup &st, const Problem<T> &pr, const ChartId &id) {
  ChartT<T> ch;
  using P = PolyT<T>;
  const P mu = P::Var(0), tau = P::Var(1);
  const P p[3] = {P::Var(2), P::Var(3), P::Var(4)};
  const T one(1), two(2);
  const V3<T> ne1 = VScale(Zero<T>() - one, pr.e1), ne2 = VScale(Zero<T>() - one, pr.e2);
  V3<T> A, B;
  if (id.side == 0) { A = pr.e1; B = pr.e2; }
  else if (id.side == 1) { A = ne1; B = pr.e2; }
  else if (id.side == 2) { A = pr.e2; B = pr.e1; }
  else { A = ne2; B = pr.e1; }
  const PVecT<T> a = PConst(A) + tau * PConst(B);
  // Which chart variable (p index) gives each coordinate (-1: fixed by the face).
  int pvar[3] = {-1, -1, -1};
  if (id.kind == "Fe") {
    for (int i = 0; i < 3; i++) pvar[i] = i;
  } else {
    int o = 0;
    for (int i = 0; i < 3; i++) if (i != id.axis) pvar[i] = 1 + o++;
  }
  P pv[3] = {p[0], p[1], p[2]};
  if (id.ratio == 1) {
    for (int i = 0; i < 3; i++) if (!st.Strong(i) && pvar[i] >= 0) pv[pvar[i]] = mu * p[pvar[i]];
  } else if (id.ratio == 2) {
    const int k = pvar[id.ratio_coord];
    CHECK(k >= 0);
    const T Z = ScaleT<T>(st.Z(id.kind, id.side, id.axis, id.sign)), sg = id.ratio_sign > 0 ? one : Zero<T>() - one;
    pv[k] = sg * (Z * mu + p[k]);
  }
  P e = P::Const(one), s[3];
  if (id.kind == "Fe") {
    for (int i = 0; i < 3; i++) s[i] = pv[i];
  } else if (id.kind == "cone" || id.kind == "Mcone") {
    // s = s_center + t sigma, sigma on the cube face (axis, sign).
    P center[3];
    if (id.kind == "Mcone") {
      if (st.aniso) {
        center[0] = P::Const(one);
      } else {
        const V3<T> XA = VCross(pr.x, A), XB = VCross(pr.x, B);
        center[0] = P::Const(VDot(XA, pr.e1)) + VDot(XB, pr.e1) * tau;
        center[1] = P::Const(VDot(XA, pr.e2)) + VDot(XB, pr.e2) * tau;
      }
    }
    int o = 0;
    for (int i = 0; i < 3; i++) {
      const P sig = i == id.axis ? P::Const(id.sign > 0 ? one : Zero<T>() - one) : pv[1 + o++];
      const T sc = ScaleT<T>(st.ConeScale(id.kind, i));
      s[i] = center[i] + (sc * p[0]) * sig;
    }
  } else {
    e = p[0];
    int o = 0;
    for (int i = 0; i < 3; i++) {
      const T r = ScaleT<T>(st.Range(i));
      s[i] = i == id.axis ? P::Const(id.sign > 0 ? r : Zero<T>() - r) : pv[1 + o++];
    }
    if (id.ratio >= 10) {
      CHECK(id.axis != 0);
      const int zi = st.Z(id.kind, id.side, id.axis, id.sign);
      const T Z = ScaleT<T>(zi), Z2 = ScaleT<T>(st.tie_ratio), K = ScaleT<T>(st.TieK(zi)),
              Kp = ScaleT<T>(st.TieKp(zi)), m1 = Zero<T>() - one;
      const P q = p[1];
      switch (id.ratio) {
        case 10: e = mu * p[0]; s[0] = mu * q; break;
        case 11: e = mu * p[0]; s[0] = Kp * mu + q; break;
        case 12: e = mu * p[0]; s[0] = m1 * (Kp * mu + q); break;
        case 13: e = K * mu + p[0]; s[0] = mu * q; break;
        case 14: e = K * mu + p[0]; s[0] = m1 * (Z * mu + q); break;
        case 15: e = K * mu + p[0]; s[0] = e + mu * q; break;
        case 16: e = K * mu + p[0]; s[0] = e + Z2 * mu + q; break;
        default: e = K * mu + p[0]; s[0] = Z * mu + q * (p[0] + (K - Z - Z2) * mu); break;
      }
    } else if (id.ratio >= 3) {
      CHECK(id.ratio_coord == 0 && id.axis != 0);
      const T Z = ScaleT<T>(st.Z(id.kind, id.side, id.axis, id.sign)), Z2 = ScaleT<T>(st.tie_ratio);
      const P q = p[1];  // s0's chart variable (axis != 0)
      if (id.ratio == 3) {
        e = (Z - Z2) * mu + p[0];
        s[0] = e + mu * q;
      } else if (id.ratio == 4) {
        e = (Z - Z2) * mu + p[0];
        s[0] = e + Z2 * mu + q;
      } else if (id.ratio == 6) {
        e = mu * p[0];
        s[0] = Z * mu + q;
      } else {
        e = (Z + Z2) * mu + p[0];
        s[0] = Z * mu + q * p[0];
      }
    }
  }
  ch.u = PConst(pr.x) + (mu * e) * a;
  if (st.aniso) {
    const PVecT<T> m = PCross(PConst(pr.x), a);
    ch.w = (mu * s[0]) * m + ((mu * mu) * s[1]) * a + ((mu * mu) * s[2]) * PConst(pr.x);
  } else {
    ch.w = (mu * s[0]) * PConst(pr.e1) + (mu * s[1]) * PConst(pr.e2) + ((mu * mu) * s[2]) * PConst(pr.x);
  }
  if (st.half_turn) {
    // |x|^2 (2 u^T N G u - |u|^2 (tr(N G) + tr N)) with G = H_x = 2 x x^T / |x|^2 - I:
    // 2 u^T N G' u - |u|^2 (tr(N G') + |x|^2 tr N), G' = 2 x x^T - |x|^2 I.
    const T xx = VDot(pr.x, pr.x);
    const P ww = PDot(ch.w, ch.w), one_m = P::Const(one) - ww;
    auto Nvec = [&](const V3<T> &v) {
      return one_m * PConst(v) + (two * PDot(ch.w, v)) * ch.w + two * PCross(ch.w, PConst(v));
    };
    std::array<PVecT<T>, 3> NGcol, Ncol;
    for (int j = 0; j < 3; j++) {
      V3<T> g, ej{Zero<T>(), Zero<T>(), Zero<T>()};
      ej[j] = one;
      for (int i = 0; i < 3; i++) g[i] = two * pr.x[i] * pr.x[j] - (i == j ? xx : Zero<T>());
      NGcol[j] = Nvec(g);
      Ncol[j] = Nvec(ej);
    }
    PVecT<T> NGu;
    for (int i = 0; i < 3; i++) NGu[i] = NGcol[0][i] * ch.u[0] + NGcol[1][i] * ch.u[1] + NGcol[2][i] * ch.u[2];
    P cell = two * PDot(ch.u, NGu) - PDot(ch.u, ch.u) * (NGcol[0][0] + NGcol[1][1] + NGcol[2][2] +
                                                          xx * (Ncol[0][0] + Ncol[1][1] + Ncol[2][2]));
    cell = DivideVar(cell, 0);
    if (id.kind == "cone" || id.kind == "Mcone") cell = DivideVar(cell, 2);
    ch.cell = cell;
  }
  return ch;
}

template <class T>
std::vector<PolyT<T>> WitnessPolys(const Problem<T> &pr, const ChartT<T> &ch, bool cone, const V3<T> &vk,
                                   const V3<T> &vkp, const V3<T> &c) {
  using P = PolyT<T>;
  const T one(1), two(2);
  const P ww = PDot(ch.w, ch.w), D = P::Const(one) + ww;
  const V3<T> dv = VSub(vk, vkp);
  const PVecT<T> Ndv = (P::Const(one) - ww) * PConst(dv) + (two * PDot(ch.w, dv)) * ch.w + two * PCross(ch.w, PConst(dv));
  const PVecT<T> d = PCross(ch.u, PConst(c));
  const P base = PDot(Ndv, d);
  const PVecT<T> Dd = {D * d[0], D * d[1], D * d[2]};
  std::vector<P> out;
  for (const V3<T> &vj : pr.V)
    for (const V3<T> &vjp : pr.V) {
      P q = base - PDot(Dd, VSub(vj, vjp));
      q = DivideVar(q, 0);
      if (cone) q = DivideVar(q, 2);
      out.push_back(q);
    }
  return out;
}

struct Stats { std::atomic<int64_t> ok{0}, pruned{0}, failed{0}; };

struct Certifier {
  const Setup &st;
  ChartId id;
  bool exact;
  int max_depth;
  Stats *stats;
  ChartT<double> chd;
  std::unique_ptr<ChartT<KNum>> chk;
  Dense cell;
  std::vector<std::unique_ptr<std::vector<Dense>>> cache;
  std::vector<std::unique_ptr<std::vector<DenseK>>> kcache;  // exact mode: the exact polynomials
  std::mutex mu;
  std::vector<std::string> fail_boxes;

  Certifier(const Setup &s, const ChartId &i, bool ex, int md, Stats *stt)
      : st(s), id(i), exact(ex), max_depth(md), stats(stt) {
    chd = MakeChart(st, st.pd, id);
    if (exact) {
      chk = std::make_unique<ChartT<KNum>>(MakeChart(st, st.pk, id));
      if (!chk->cell.t.empty()) cell = ToDense(chk->cell);
    } else if (!chd.cell.t.empty()) {
      cell = ToDense(chd.cell);
    }
    cache.resize(st.pd.W.size());
    kcache.resize(st.pd.W.size());
  }
  bool Cone() const { return id.kind == "cone" || id.kind == "Mcone"; }

  const std::vector<Dense> &Get(int wi) {
    {
      std::lock_guard<std::mutex> l(mu);
      if (cache[wi]) return *cache[wi];
    }
    std::vector<Dense> ds;
    if (exact) {
      const auto &w = st.pk.W[wi];
      for (const auto &p : WitnessPolys(st.pk, *chk, Cone(), st.pk.V[w.k], st.pk.V[w.kp], w.c)) ds.push_back(ToDense(p));
    } else {
      const auto &w = st.pd.W[wi];
      for (const auto &p : WitnessPolys(st.pd, chd, Cone(), st.pd.V[w.k], st.pd.V[w.kp], w.c)) ds.push_back(ToDense(p));
    }
    std::lock_guard<std::mutex> l(mu);
    if (!cache[wi]) cache[wi] = std::make_unique<std::vector<Dense>>(std::move(ds));
    return *cache[wi];
  }
  const std::vector<DenseK> &GetK(int wi) {
    {
      std::lock_guard<std::mutex> l(mu);
      if (kcache[wi]) return *kcache[wi];
    }
    std::vector<DenseK> ds;
    const auto &w = st.pk.W[wi];
    for (const auto &p : WitnessPolys(st.pk, *chk, Cone(), st.pk.V[w.k], st.pk.V[w.kp], w.c)) ds.push_back(ToDenseK(p));
    std::lock_guard<std::mutex> l(mu);
    if (!kcache[wi]) kcache[wi] = std::make_unique<std::vector<DenseK>>(std::move(ds));
    return *kcache[wi];
  }

  // The interval of chart coordinate s_i over the box (Fe charts, any ratio mode).
  std::pair<double, double> SRange(const Box &box, int i) const {
    const auto v = box[2 + i];
    if (id.ratio == 0 || st.Strong(i)) return v;
    const double m0 = box[0].first, m1 = box[0].second;
    if (id.ratio == 1) {
      const double c[4] = {m0 * v.first, m0 * v.second, m1 * v.first, m1 * v.second};
      return {*std::min_element(c, c + 4), *std::max_element(c, c + 4)};
    }
    if (i != id.ratio_coord) return v;
    const double z = st.Z(id.kind, id.side, id.axis, id.sign);
    const double lo = z * m0 + v.first, hi = z * m1 + v.second;
    return id.ratio_sign > 0 ? std::pair<double, double>{lo, hi} : std::pair<double, double>{-hi, -lo};
  }

  bool InCone(const Box &box) const {
    if (id.kind != "Fe") return false;
    // The cones cover |s_i - center_i| <= t0 * Range(i) / 2.
    auto within = [&](int i, double c, double t, const char *kind) {
      const auto r = SRange(box, i);
      const double rad = t * st.ConeScale(kind, i);
      return std::max(std::abs(r.first - c), std::abs(r.second - c)) <= rad;
    };
    if (within(0, 0, st.t0, "cone") && within(1, 0, st.t0, "cone") && within(2, 0, st.t0, "cone")) return true;
    if (!st.tie_cones || !st.aniso) return false;
    // Anisotropic: the M-cone is centered at s = (1, 0, 0), radius t0m.
    return within(0, 1, st.t0m, "Mcone") && within(1, 0, st.t0m, "Mcone") && within(2, 0, st.t0m, "Mcone");
  }

  // Certifies the box; appends its certificate tree to *out (preorder: 'X' inside a
  // cone chart, 'P' outside the half-turn cell, 'L<witness>,' a witness leaf, 'F'
  // failed, 'S<axis>' a split at the midpoint followed by the two halves).
  bool Rec(Box box, int depth, std::string *out) {
    if (InCone(box)) { *out += 'X'; return true; }
    if (!cell.c.empty() && BernsteinLower(cell, box) > 0) { stats->pruned++; *out += 'P'; return true; }
    // Screen witnesses by their worst value over the box's center and its 2 NV
    // face centers (a witness valid on only part of the box ranks low).
    std::vector<std::array<double, NV>> pts;
    {
      std::array<double, NV> c;
      for (int i = 0; i < NV; i++) c[i] = 0.5 * (box[i].first + box[i].second);
      pts.push_back(c);
      for (int i = 0; i < NV; i++) {
        auto lo = c, hi = c;
        lo[i] = box[i].first;
        hi[i] = box[i].second;
        pts.push_back(lo);
        pts.push_back(hi);
      }
    }
    std::vector<std::pair<double, int>> sc(st.pd.W.size(), {INFINITY, 0});
    for (size_t wi = 0; wi < st.pd.W.size(); wi++) sc[wi].second = wi;
    for (const auto &x : pts) {
      V3<double> u, w;
      for (int a = 0; a < 3; a++) { u[a] = EvalD(chd.u[a], x.data()); w[a] = EvalD(chd.w[a], x.data()); }
      const double ww = VDot(w, w), Dw = 1 + ww;
      // Rotated support vertices, once per point.
      std::vector<V3<double>> rv(st.pd.V.size());
      for (size_t k = 0; k < st.pd.V.size(); k++) {
        const V3<double> &v = st.pd.V[k];
        const V3<double> wv = VCross(w, v);
        for (int a = 0; a < 3; a++) rv[k][a] = ((1 - ww) * v[a] + 2 * w[a] * VDot(w, v) + 2 * wv[a]) / Dw;
      }
      for (size_t wi = 0; wi < st.pd.W.size(); wi++) {
        const V3<double> d = VCross(u, st.pd.W[wi].c);
        double mx = -1e300, mn = 1e300;
        for (const auto &vj : st.pd.V) { mx = std::max(mx, VDot(vj, d)); mn = std::min(mn, VDot(vj, d)); }
        const double v = (VDot(rv[st.pd.W[wi].k], d) - VDot(rv[st.pd.W[wi].kp], d) - (mx - mn)) /
                         std::sqrt(VDot(d, d));
        sc[wi].first = std::min(sc[wi].first, v);
      }
    }
    const int ntry = std::min<int>(g_try, sc.size());
    std::partial_sort(sc.begin(), sc.begin() + ntry, sc.end(), [](auto &a, auto &b) { return a.first > b.first; });
    for (int r = 0; r < ntry; r++) {
      if (sc[r].first <= -1e-9) break;
      const auto &ds = Get(sc[r].second);
      bool all = true;
      for (size_t j = 0; j < ds.size(); j++) {
        // Non-strict: P >= 0 suffices. Exact mode: rigorous (exact zeros stay 0);
        // a slightly negative interval bound (a coefficient that vanishes by
        // cancellation) is redone with exact coefficients. Double mode: allows
        // rounding noise (feasibility only).
        const double lb = BernsteinLower(ds[j], box);
        bool ok = exact ? lb >= 0 : lb >= -1e-13;
        if (!ok && exact && lb > -1e-9) {
          std::array<std::pair<Q, Q>, NV> qb;
          for (int i = 0; i < NV; i++) qb[i] = {DyadicRat(box[i].first), DyadicRat(box[i].second)};
          ok = !(ExactBernsteinLower(GetK(sc[r].second)[j], qb) < Q(0));
        }
        if (!ok) { all = false; break; }
      }
      if (all) { stats->ok++; *out += 'L' + std::to_string(sc[r].second) + ','; return true; }
    }
    if (depth >= max_depth) {
      stats->failed++;
      *out += 'F';
      std::lock_guard<std::mutex> l(mu);
      if (fail_boxes.size() < 5) {
        std::string s;
        for (auto &[lo, hi] : box) s += std::to_string(lo) + ".." + std::to_string(hi) + " ";
        fail_boxes.push_back(s);
      }
      return false;
    }
    int best = 0;
    double bw = -1;
    for (int i = 0; i < NV; i++) {
      const double rel = (box[i].second - box[i].first) / (id.box[i].second - id.box[i].first);
      if (rel > bw) { bw = rel; best = i; }
    }
    const double m = 0.5 * (box[best].first + box[best].second);
    auto b1 = box, b2 = box;
    b1[best].second = m;
    b2[best].first = m;
    *out += 'S' + std::to_string(best);
    const bool r1 = Rec(b1, depth + 1, out);
    const bool r2 = Rec(b2, depth + 1, out);
    return r1 && r2;
  }
};

}  // namespace

int main(int argc, char **argv) {
  std::fesetround(FE_TONEAREST);
  InitConstants();
  std::string cap = "n", only;
  int max_depth = 30, threads = 60;
  bool aniso = false, exact = true, mix = true;
  std::string debug_box, point;
  bool frame_only = false;
  double t0m = 0.25;
  int mcm = 1;
  std::string export_file;
  std::map<std::string, int> z_override;
  int ratio_z = 0, ratio_z_face = 0, tie_ratio = 0, tie_k = 0, tie_kp = 0;
  std::set<std::string> tie_charts;
  double strong_scale = 2;
  Q mu0(1, 64);
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--cap") cap = next();
    else if (a == "--model") g_model = next();
    else if (a == "--mu0") mu0 = Q(std::string_view(next()));
    else if (a == "--max_depth") max_depth = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--try") g_try = std::stoi(next());
    else if (a == "--aniso") aniso = true;
    else if (a == "--only") only = next();
    else if (a == "--double") exact = false;
    else if (a == "--no_mix") mix = false;
    else if (a == "--strong_scale") strong_scale = std::stod(next());
    else if (a == "--debug_box") debug_box = next();
    else if (a == "--point") point = next();
    else if (a == "--frame_only") frame_only = true;
    else if (a == "--t0_mcone") t0m = std::stod(next());
    else if (a == "--mcone_strong_mul") mcm = std::stoi(next());
    else if (a == "--z_override") {
      std::stringstream ss(next());
      std::string item;
      while (std::getline(ss, item, ',')) {
        const size_t eq = item.find('=');
        CHECK(eq != std::string::npos) << item;
        z_override[item.substr(0, eq)] = std::stoi(item.substr(eq + 1));
      }
    }
    else if (a == "--export") export_file = next();
    else if (a == "--ratio_z") ratio_z = std::stoi(next());
    else if (a == "--ratio_z_face") ratio_z_face = std::stoi(next());
    else if (a == "--tie_ratio") tie_ratio = std::stoi(next());
    else if (a == "--tie_charts") {
      std::stringstream ss(next());
      std::string item;
      while (std::getline(ss, item, ',')) tie_charts.insert(item);
    }
    else if (a == "--tie_k") tie_k = std::stoi(next());
    else if (a == "--tie_kp") tie_kp = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  Setup st;
  LoadSolid(&st);
  st.mu0 = mu0.ToDouble();
  // mu0 should be dyadic (41/512 by default) so that box endpoints are exact doubles.
  st.aniso = aniso;
  st.strong_scale = strong_scale;
  st.ratio_z = ratio_z;
  st.ratio_z_face = ratio_z_face;
  st.tie_ratio = tie_ratio;
  st.tie_charts = tie_charts;
  st.tie_k = tie_k;
  st.tie_kp = tie_kp;
  st.t0m = t0m;
  st.mcm = mcm;
  st.z_override = z_override;
  // The rational frame at the mirror normal x = (1,0,-1) (Q = H_x = -(the swap of
  // coordinates 0 and 2) = mirrorQMat 1).
  CHECK(cap == "n") << "--cap n";
  auto kq = [](int a) { return KNum{Q(a), Q(0), Q(0), Q(0)}; };
  st.pk.x = {kq(1), kq(0), kq(-1)};
  st.pk.e1 = {kq(0), kq(1), kq(0)};
  st.pk.e2 = {kq(1), kq(0), kq(1)};
  st.half_turn = true;
  auto todbl = [](const V3<KNum> &v) { return V3<double>{ToDouble(v[0]), ToDouble(v[1]), ToDouble(v[2])}; };
  st.pd.x = todbl(st.pk.x);
  st.pd.e1 = todbl(st.pk.e1);
  st.pd.e2 = todbl(st.pk.e2);
  const std::vector<int> supp = SupportVertices(st.pd.V, st.pd.x);
  std::vector<std::vector<int>> nb(st.pd.V.size());
  for (auto &[a, b] : st.edges) { nb[a].push_back(b); nb[b].push_back(a); }
  // Width witnesses: for each support vertex k at x and each candidate direction c
  // (edges at k, chords to the other support vertices, and mixtures of angularly
  // adjacent ones, as in capcert), k' = every support vertex minimizing <v, x cross c>
  // up to 1e-9 (several when the opposite side of the silhouette is an edge).
  auto add = [&](int k, const V3<KNum> &c) {
    const V3<double> d = VCross(st.pd.x, todbl(c));
    // d = u x c must stay away from 0 over the cap: skip c = 0 (the mixture of a
    // chord parallel to x with its negative) and c nearly parallel to x.
    const V3<double> cd = todbl(c);
    if (VDot(cd, cd) == 0 || VDot(d, d) < 0.01 * VDot(st.pd.x, st.pd.x) * VDot(cd, cd)) return;
    double mn = 1e300;
    for (int m : supp) mn = std::min(mn, VDot(st.pd.V[m], d));
    for (int m : supp)
      if (VDot(st.pd.V[m], d) <= mn + 1e-9 * std::sqrt(VDot(d, d)) && m != k) {
        st.pk.W.push_back({k, m, c});
        st.pd.W.push_back({k, m, todbl(c)});
      }
  };
  for (int k : supp) {
    std::vector<int> others = nb[k];
    for (int m : supp) if (m != k && std::find(others.begin(), others.end(), m) == others.end()) others.push_back(m);
    std::vector<V3<KNum>> dirs;
    for (int m : others) {
      for (int sg : {1, -1}) {
        const V3<KNum> ck = sg > 0 ? VSub(st.pk.V[m], st.pk.V[k]) : VSub(st.pk.V[k], st.pk.V[m]);
        dirs.push_back(ck);
        add(k, ck);
      }
    }
    if (mix) {
      std::vector<std::pair<double, int>> ang;
      const V3<double> f1 = st.pd.e1, f2 = st.pd.e2;
      for (size_t i = 0; i < dirs.size(); i++) {
        const V3<double> d = VCross(st.pd.x, todbl(dirs[i]));
        ang.push_back({std::atan2(VDot(d, f2), VDot(d, f1)), (int)i});
      }
      std::sort(ang.begin(), ang.end());
      for (size_t i = 0; i < ang.size(); i++) {
        const V3<KNum> &c1 = dirs[ang[i].second], &c2 = dirs[ang[(i + 1) % ang.size()].second];
        for (auto [w1, w2] : {std::pair<int, int>{1, 1}, {1, 2}, {2, 1}}) {
          const V3<KNum> c = {KNum(w1) * c1[0] + KNum(w2) * c2[0], KNum(w1) * c1[1] + KNum(w2) * c2[1],
                              KNum(w1) * c1[2] + KNum(w2) * c2[2]};
          add(k, c);
        }
      }
    }
  }
  printf("support vertices at x:");
  for (int k : supp) printf(" %d", k);
  printf("\n");
  printf("cap %s (%s, %s): %zu vertices, %zu support vertices, %zu witnesses, mu0 %s\n", cap.c_str(),
         aniso ? "anisotropic" : "isotropic", exact ? "exact" : "double", st.pd.V.size(), supp.size(),
         st.pd.W.size(), mu0.ToString().c_str());
  printf("frame %.17g %.17g %.17g  %.17g %.17g %.17g  %.17g %.17g %.17g\n", st.pd.x[0], st.pd.x[1], st.pd.x[2],
         st.pd.e1[0], st.pd.e1[1], st.pd.e1[2], st.pd.e2[0], st.pd.e2[1], st.pd.e2[2]);
  {
    // The exact frame (each coordinate a + b sqrt5 + c s + d s sqrt5, s = sin 72): dh_caps.py.
    std::string kf = "kframe";
    for (const V3<KNum> *v : {&st.pk.x, &st.pk.e1, &st.pk.e2})
      for (int a = 0; a < 3; a++)
        for (const Q *q : {&(*v)[a].a, &(*v)[a].b, &(*v)[a].c, &(*v)[a].d}) kf += " " + q->ToString();
    printf("%s\n", kf.c_str());
  }
  fflush(stdout);
  if (frame_only) return 0;

  std::vector<ChartId> charts;
  for (int side = 0; side < 4; side++) {
    charts.push_back({"Fe", side, 0, 1, {{{0, st.mu0}, {-1, 1}, {-st.Range(0), st.Range(0)}, {-st.Range(1), st.Range(1)},
                                            {-st.Range(2), st.Range(2)}}}});
    for (int ax = 0; ax < 3; ax++)
      for (double sg : {1.0, -1.0}) {
        charts.push_back({"cone", side, ax, sg, {{{0, st.mu0}, {-1, 1}, {0, st.t0}, {-1, 1}, {-1, 1}}}});
        if (st.tie_cones) charts.push_back({"Mcone", side, ax, sg, {{{0, st.mu0}, {-1, 1}, {0, st.t0m}, {-1, 1}, {-1, 1}}}});
        {
          // The two free coordinates of face `ax` (in order).
          std::vector<int> fr;
          for (int i = 0; i < 3; i++) if (i != ax) fr.push_back(i);
          charts.push_back({"face", side, ax, sg, {{{0, st.mu0}, {-1, 1}, {0, 1}, {-st.Range(fr[0]), st.Range(fr[0])},
                                                     {-st.Range(fr[1]), st.Range(fr[1])}}}});
        }
      }
  }
  if (st.ratio_z > 0) {
    // Replace each chart dominated by a strong coordinate (Fe, and faces/cones
    // whose axis is strong) by its ratio blow-ups.
    std::vector<ChartId> out;
    for (const ChartId &c : charts) {
      const bool strong_dom = c.kind == "Fe" || st.Strong(c.axis);
      if (!strong_dom) { out.push_back(c); continue; }
      if (st.tie_charts.count(c.kind + ":" + std::to_string(c.side) + ":" + std::to_string(c.axis) + ":" +
                              (c.sign > 0 ? "1" : "-1"))) {
        CHECK(c.kind == "face" && c.axis != 0 && st.tie_ratio > 0);
        const int z = st.Z(c.kind, c.side, c.axis, c.sign), z2 = st.tie_ratio, k = st.TieK(z), kp = st.TieKp(z);
        CHECK(k >= z + z2 && kp > k) << "tie scheme needs K >= Z + Z2, K' > K";
        const std::pair<double, double> boxes[8][2] = {
            {{0, (double)k}, {-(double)kp, (double)kp}}, {{0, (double)k}, {0, 2}}, {{0, (double)k}, {0, 2}},
            {{0, 1}, {-(double)z, (double)z}}, {{0, 1}, {0, 2}}, {{0, 1}, {-(double)z2, (double)z2}},
            {{0, 1}, {0, 2}}, {{0, 1}, {0, 1}}};
        for (int m = 0; m < 8; m++) {
          ChartId o = c;
          o.ratio = 10 + m;
          o.box[2] = boxes[m][0];
          o.box[3] = boxes[m][1];
          out.push_back(o);
        }
        continue;
      }
      auto pidx = [&](int i) {
        if (c.kind == "Fe") return i;
        int o = 0;
        for (int j = 0; j < 3; j++) { if (j == c.axis) continue; if (j == i) return 1 + o; o++; }
        return -1;
      };
      ChartId in = c;
      in.ratio = 1;
      for (int i = 0; i < 3; i++)
        if (!st.Strong(i) && pidx(i) >= 0) in.box[2 + pidx(i)] = {-(double)st.Z(c.kind, c.side, c.axis, c.sign), (double)st.Z(c.kind, c.side, c.axis, c.sign)};
      out.push_back(in);
      for (int i = 0; i < 3; i++) {
        if (st.Strong(i) || pidx(i) < 0) continue;
        for (double sg : {1.0, -1.0}) {
          ChartId o = c;
          o.ratio = 2;
          o.ratio_coord = i;
          o.ratio_sign = sg;
          o.box[2 + pidx(i)] = {0, c.box[2 + pidx(i)].second};
          if (st.tie_ratio > 0 && st.tie_charts.empty() && c.kind == "face" && c.side == 2 && i == 0 && sg > 0) {
            // Tie-centred replacement of s0 >= Z mu (see ChartId).
            const double z2 = st.tie_ratio;
            const double z = st.Z(c.kind, c.side, c.axis, c.sign);
            CHECK(z > z2);
            ChartId b = o, f = o, g = o, m = o;
            b.ratio = 3; b.box[2] = {0, 1}; b.box[2 + pidx(i)] = {-z2, z2};
            f.ratio = 4; f.box[2] = {0, 1}; f.box[2 + pidx(i)] = {0, 2};
            g.ratio = 6; g.box[2] = {0, z - z2}; g.box[2 + pidx(i)] = {0, 2};
            m.ratio = 5; m.box[2] = {0, 1}; m.box[2 + pidx(i)] = {0, 1};
            out.push_back(b); out.push_back(f); out.push_back(g); out.push_back(m);
            continue;
          }
          out.push_back(o);
        }
      }
    }
    charts = out;
  }
  struct Task { size_t chart; Box box; };
  std::vector<Task> tasks;
  std::vector<std::unique_ptr<Certifier>> certs(charts.size());
  std::vector<std::unique_ptr<Stats>> stats(charts.size());
  std::vector<std::atomic<int>> pending(charts.size());
  std::vector<std::atomic<bool>> chart_ok(charts.size());
  for (size_t k = 0; k < charts.size(); k++) {
    const ChartId &ch = charts[k];
    if (!only.empty()) {
      const std::string idstr = ch.kind + ":" + std::to_string(ch.side) + ":" + std::to_string(ch.axis) + ":" +
                                (ch.sign > 0 ? "1" : "-1");
      bool match = false;
      std::stringstream ss(only);
      std::string item;
      while (std::getline(ss, item, ',')) match = match || idstr.rfind(item, 0) == 0;
      if (!match) continue;
    }
    stats[k] = std::make_unique<Stats>();
    certs[k] = std::make_unique<Certifier>(st, ch, exact, max_depth, stats[k].get());
    chart_ok[k] = true;
    pending[k] = 16;
    for (int i = 0; i < 4; i++)
      for (int j = 0; j < 4; j++) {
        Box b = ch.box;
        const double m0 = b[0].first, m1 = b[0].second, t0 = b[1].first, t1 = b[1].second;
        b[0] = {m0 + (m1 - m0) * i / 4, m0 + (m1 - m0) * (i + 1) / 4};
        b[1] = {t0 + (t1 - t0) * j / 4, t0 + (t1 - t0) * (j + 1) / 4};
        tasks.push_back({k, b});
      }
  }
  if (!point.empty()) {
    // --point "kind:side:axis:sign p0 p1 p2 p3 p4": the pose (u, w) at that chart point.
    std::stringstream ss(point);
    std::string idstr;
    ss >> idstr;
    std::array<double, NV> x;
    for (int i = 0; i < NV; i++) CHECK(ss >> x[i]);
    for (const ChartId &ch : charts) {
      const std::string id2 = ch.kind + ":" + std::to_string(ch.side) + ":" + std::to_string(ch.axis) + ":" +
                              (ch.sign > 0 ? "1" : "-1");
      if (id2 != idstr || ch.ratio != 0) continue;
      const ChartT<double> c = MakeChart(st, st.pd, ch);
      printf("pose u %.17g %.17g %.17g w %.17g %.17g %.17g cell %.6e\n", EvalD(c.u[0], x.data()), EvalD(c.u[1], x.data()),
             EvalD(c.u[2], x.data()), EvalD(c.w[0], x.data()), EvalD(c.w[1], x.data()), EvalD(c.w[2], x.data()),
             c.cell.t.empty() ? 0.0 : EvalD(c.cell, x.data()));
      break;
    }
    return 0;
  }
  if (!debug_box.empty()) {
    // --debug_box "kind:side:axis:sign lo,hi lo,hi lo,hi lo,hi lo,hi": every witness on that box.
    std::stringstream ss(debug_box);
    std::string idstr;
    ss >> idstr;
    Box b;
    for (int i = 0; i < NV; i++) {
      std::string r;
      ss >> r;
      CHECK(std::sscanf(r.c_str(), "%lf,%lf", &b[i].first, &b[i].second) == 2) << r;
    }
    for (size_t k = 0; k < charts.size(); k++) {
      const ChartId &ch = charts[k];
      const std::string id2 = ch.kind + ":" + std::to_string(ch.side) + ":" + std::to_string(ch.axis) + ":" +
                              (ch.sign > 0 ? "1" : "-1");
      if (id2 != idstr) continue;
      printf("chart %s side %d axis %d sign %+.0f ratio %d/%d%+.0f\n", ch.kind.c_str(), ch.side, ch.axis, ch.sign,
             ch.ratio, ch.ratio_coord, ch.ratio_sign);
      Stats s0;
      Certifier cert(st, ch, exact, max_depth, &s0);
      std::vector<std::tuple<double, int, int>> res;
      for (size_t wi = 0; wi < st.pd.W.size(); wi++) {
        const auto &ds = cert.Get(wi);
        double worst = INFINITY;
        int wj = -1;
        for (size_t j = 0; j < ds.size(); j++) {
          const double lb = BernsteinLower(ds[j], b);
          if (lb < worst) { worst = lb; wj = j; }
        }
        res.push_back({worst, (int)wi, wj});
      }
      std::sort(res.rbegin(), res.rend());
      std::map<int, int> shown;
      for (int r = 0; r < (int)res.size(); r++) {
        const auto [v, wi, wj] = res[r];
        const int kk = st.pd.W[wi].k;
        if (r < 12 || shown[kk] < 1) {
          shown[kk]++;
          const auto &W = st.pd.W[wi];
          size_t nz = 0;
          for (const auto &dd : cert.Get(wi)) nz += dd.c.size();
          printf("witness %d (k %d k' %d c %.3f %.3f %.3f): min over j of Bernstein lower %.3e (worst j %d), %zu dense coeffs\n",
                 wi, kk, W.kp, W.c[0], W.c[1], W.c[2], v, wj, nz);
        }
      }
    }
    return 0;
  }
  std::vector<std::string> task_out(tasks.size());
  std::atomic<size_t> next{0};
  std::mutex out_mu;
  std::vector<std::thread> ts;
  for (int t = 0; t < threads; t++) {
    ts.emplace_back([&]() {
      for (;;) {
        const size_t q = next++;
        if (q >= tasks.size()) return;
        const Task &task = tasks[q];
        if (!certs[task.chart]->Rec(task.box, 4, &task_out[q])) chart_ok[task.chart] = false;
        if (--pending[task.chart] == 0) {
          const ChartId &ch = charts[task.chart];
          const Stats &s = *stats[task.chart];
          std::lock_guard<std::mutex> l(out_mu);
          printf("%-5s side %d axis %d sign %+.0f ratio %d/%d%+.0f: %s  boxes %lld pruned %lld failed %lld\n",
                 ch.kind.c_str(), ch.side, ch.axis, ch.sign, ch.ratio, ch.ratio_coord, ch.ratio_sign,
                 chart_ok[task.chart] ? "OK" : "FAIL", (long long)s.ok.load(),
                 (long long)s.pruned.load(), (long long)s.failed.load());
          for (const auto &f : certs[task.chart]->fail_boxes) printf("    fail %s\n", f.c_str());
          fflush(stdout);
        }
      }
    });
  }
  for (auto &t : ts) t.join();
  if (!export_file.empty()) {
    // The certificate for the Lean checker: the setup, the exact solid and witnesses,
    // and per chart its root box and certificate tree (the 4 x 4 task split of the
    // first two coordinates is two midpoint splits of each).
    FILE *f = fopen(export_file.c_str(), "w");
    CHECK(f != nullptr) << export_file;
    auto kq = [](const KNum &x) {
      return x.a.ToString() + " " + x.b.ToString() + " " + x.c.ToString() + " " + x.d.ToString();
    };
    auto kv = [&](const V3<KNum> &v) { return kq(v[0]) + "  " + kq(v[1]) + "  " + kq(v[2]); };
    fprintf(f, "cap %s aniso %d half_turn %d tie_cones %d mu0 %s strong_scale %s t0 %s ratio_z %d ratio_z_face %d t0_mcone %s mcone_strong_mul %d\n",
            cap.c_str(), (int)st.aniso, (int)st.half_turn, (int)st.tie_cones, mu0.ToString().c_str(),
            DyadicQ(st.strong_scale).c_str(), DyadicQ(st.t0).c_str(), st.ratio_z, st.ratio_z_face, DyadicQ(st.t0m).c_str(), st.mcm);
    fprintf(f, "frame %s  %s  %s\n", kv(st.pk.x).c_str(), kv(st.pk.e1).c_str(), kv(st.pk.e2).c_str());
    // The tie scheme's base charts (Lean Setup.tieCharts): kind side axis sign Z2 K K'.
    for (const std::string &tc : st.tie_charts) {
      std::vector<std::string> p;
      std::stringstream ss(tc);
      std::string item;
      while (std::getline(ss, item, ':')) p.push_back(item);
      CHECK(p.size() == 4) << tc;
      const int z = st.Z(p[0], std::stoi(p[1]), std::stoi(p[2]), std::stod(p[3]));
      fprintf(f, "tie_chart %s %s %s %s %d %d %d\n", p[0].c_str(), p[1].c_str(), p[2].c_str(), p[3].c_str(),
              st.tie_ratio, st.TieK(z), st.TieKp(z));
    }
    for (size_t i = 0; i < st.pk.V.size(); i++) fprintf(f, "vertex %zu %s\n", i, kv(st.pk.V[i]).c_str());
    for (size_t i = 0; i < st.pk.W.size(); i++)
      fprintf(f, "witness %zu %d %d %s\n", i, st.pk.W[i].k, st.pk.W[i].kp, kv(st.pk.W[i].c).c_str());
    size_t q = 0;
    for (size_t k = 0; k < charts.size(); k++) {
      if (!certs[k]) continue;
      const ChartId &ch = charts[k];
      if (!chart_ok[k]) printf("warning: exporting failed chart %s %d %d %+.0f ratio %d/%d (its tree has F leaves)\n",
                               ch.kind.c_str(), ch.side, ch.axis, ch.sign, ch.ratio, ch.ratio_coord);
      std::string box;
      for (const auto &[lo, hi] : ch.box) box += " " + DyadicQ(lo) + " " + DyadicQ(hi);
      fprintf(f, "chart %s %d %d %d %d %d %d z %d%s\n", ch.kind.c_str(), ch.side, ch.axis, ch.sign > 0 ? 1 : -1, ch.ratio,
              ch.ratio_coord, ch.ratio_sign > 0 ? 1 : -1, st.Z(ch.kind, ch.side, ch.axis, ch.sign), box.c_str());
      CHECK(tasks[q].chart == k);
      auto t = [&](int i, int j) { return task_out[q + 4 * i + j]; };
      auto quarter = [&](int i) { return "S1S1" + t(i, 0) + t(i, 1) + "S1" + t(i, 2) + t(i, 3); };
      fprintf(f, "tree S0S0%s%sS0%s%s\n", quarter(0).c_str(), quarter(1).c_str(), quarter(2).c_str(),
              quarter(3).c_str());
      q += 16;
    }
    fclose(f);
    printf("exported %s\n", export_file.c_str());
  }
  return 0;
}
