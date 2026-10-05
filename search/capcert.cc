// capcert: cap certificates for the deltoidal hexecontahedron's special views
// (the 2-fold axis view u0 and the two-kite view ux; notes/T.md). Near such a
// view x the identity's first-order cage degenerates (and at ux the pinning
// ties M(u) = H_u H_x approach the identity), so the poses (view u = x + mu e a,
// Cayley rotation w) are blown up in weighted coordinates:
//   u0 (isotropic):   w = mu (s1 e1 + s2 e2) + mu^2 s3 x
//   ux (--aniso):     w = mu s1 (x cross a) + mu^2 (s2 a + s3 x)
// (the tie direction x cross a has weight 1, the strongly blocked directions
// weight 2), with charts on the faces of the weighted cube max(e, |s|/2) = 1,
// a cone chart at the identity and, at ux, one at the tie s = (1, 0, 0). The
// domain covered is {|u - x|_inf <= mu0 (tangent coordinates), weak components
// <= 2 mu0, strong components <= 2 mu0^2}.
//
// Each box of a chart is certified by a witness (vertex k, direction c):
// P_j = (N(w) v_k - D(w) v_j) . (u x c) >= 0 for every vertex j, after
// dividing by the largest powers of mu (and of the cone radius t) that divide
// it; then h_{RK}(d) >= h_K(d) for d = u x c, so the pose is not a passage.
// The check is non-strict (a tie is not a passage). At u0 boxes outside the
// half-turn cell (g = H_x) are pruned.
//
// Witnesses are screened in double precision. By default the certificate is
// exact: the polynomials are built over K = Q(sqrt5, sin 72) from the exact
// solid (dh_exact.txt), the divisions are checked exactly (the vanishing
// coefficients must be exactly 0), and the boxes are bounded by tensor
// Bernstein coefficients in outward-rounded interval arithmetic (exact zeros
// stay exactly 0). --double runs the floating-point version (feasibility).
//
// Usage: capcert.exe [--cap u0|ux] [--aniso] [--mu0 41/512] [--max_depth 30]
//          [--threads 60] [--try 24] [--only kind:side:axis:sign,...] [--double] [--frame_only] [--z_override kind:side:axis:sign=Z,...] [--t0_mcone T] [--mcone_strong_mul M]
//          [--export FILE]

#include <algorithm>
#include <array>
#include <atomic>
#include <cfenv>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <map>
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
  struct Witness { int k; V3<T> c; };
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

void LoadSolid(Setup *s) {
  // Exact vertices (distinct) from dh_exact.txt; faces from dh_model.txt.
  std::vector<V3<KNum>> slots;
  {
    std::ifstream in("dh_exact.txt");
    CHECK(in.good()) << "dh_exact.txt (python3 dh_exact.py)";
    std::string line;
    while (std::getline(in, line)) {
      std::istringstream ss(line);
      std::string tag;
      ss >> tag;
      if (tag != "kvertex") continue;
      int i;
      ss >> i;
      CHECK(i == (int)slots.size());
      slots.push_back({ParseKTok(ss), ParseKTok(ss), ParseKTok(ss)});
    }
  }
  std::vector<int> sv;
  for (const auto &p : slots) {
    int found = -1;
    for (size_t j = 0; j < s->pk.V.size(); j++) {
      const auto d = VSub(p, s->pk.V[j]);
      if (IsZero(d[0]) && IsZero(d[1]) && IsZero(d[2])) found = j;
    }
    if (found < 0) { found = s->pk.V.size(); s->pk.V.push_back(p); }
    sv.push_back(found);
  }
  for (const auto &v : s->pk.V) s->pd.V.push_back({ToDouble(v[0]), ToDouble(v[1]), ToDouble(v[2])});
  std::ifstream in("dh_model.txt");
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    if (tag != "face") continue;
    std::vector<int> f;
    int k;
    while (ss >> k) if (std::find(f.begin(), f.end(), sv[k]) == f.end()) f.push_back(sv[k]);
    V3<double> c{0, 0, 0};
    for (int v : f) for (int a = 0; a < 3; a++) c[a] += s->pd.V[v][a] / f.size();
    auto nrm = [](V3<double> a) { const double n = std::sqrt(VDot(a, a)); return V3<double>{a[0] / n, a[1] / n, a[2] / n}; };
    const V3<double> n = nrm(c), e1 = nrm(VSub(s->pd.V[f[0]], c)), e2 = VCross(n, e1);
    std::sort(f.begin(), f.end(), [&](int a, int b) {
      return std::atan2(VDot(VSub(s->pd.V[a], c), e2), VDot(VSub(s->pd.V[a], c), e1)) <
             std::atan2(VDot(VSub(s->pd.V[b], c), e2), VDot(VSub(s->pd.V[b], c), e1));
    });
    for (size_t k2 = 0; k2 < f.size(); k2++) {
      const auto e = std::minmax(f[k2], f[(k2 + 1) % f.size()]);
      if (std::find(s->edges.begin(), s->edges.end(), std::pair<int, int>(e.first, e.second)) == s->edges.end())
        s->edges.push_back({e.first, e.second});
    }
  }
  CHECK(s->pk.V.size() == 62 && s->edges.size() == 120) << s->pk.V.size() << " " << s->edges.size();
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
  }
  ch.u = PConst(pr.x) + (mu * e) * a;
  if (st.aniso) {
    const PVecT<T> m = PCross(PConst(pr.x), a);
    ch.w = (mu * s[0]) * m + ((mu * mu) * s[1]) * a + ((mu * mu) * s[2]) * PConst(pr.x);
  } else {
    ch.w = (mu * s[0]) * PConst(pr.e1) + (mu * s[1]) * PConst(pr.e2) + ((mu * mu) * s[2]) * PConst(pr.x);
  }
  if (st.half_turn) {
    // 2 u^T N G u - |u|^2 (tr(N G) + tr N), G = H_x = 2 x x^T - I (|x| = 1).
    const P ww = PDot(ch.w, ch.w), one_m = P::Const(one) - ww;
    auto Nvec = [&](const V3<T> &v) {
      return one_m * PConst(v) + (two * PDot(ch.w, v)) * ch.w + two * PCross(ch.w, PConst(v));
    };
    std::array<PVecT<T>, 3> NGcol, Ncol;
    for (int j = 0; j < 3; j++) {
      V3<T> g, ej{Zero<T>(), Zero<T>(), Zero<T>()};
      ej[j] = one;
      for (int i = 0; i < 3; i++) g[i] = two * pr.x[i] * pr.x[j] - (i == j ? one : Zero<T>());
      NGcol[j] = Nvec(g);
      Ncol[j] = Nvec(ej);
    }
    PVecT<T> NGu;
    for (int i = 0; i < 3; i++) NGu[i] = NGcol[0][i] * ch.u[0] + NGcol[1][i] * ch.u[1] + NGcol[2][i] * ch.u[2];
    P cell = two * PDot(ch.u, NGu) - PDot(ch.u, ch.u) * (NGcol[0][0] + NGcol[1][1] + NGcol[2][2] +
                                                          Ncol[0][0] + Ncol[1][1] + Ncol[2][2]);
    cell = DivideVar(cell, 0);
    if (id.kind == "cone" || id.kind == "Mcone") cell = DivideVar(cell, 2);
    ch.cell = cell;
  }
  return ch;
}

template <class T>
std::vector<PolyT<T>> WitnessPolys(const Problem<T> &pr, const ChartT<T> &ch, bool cone, const V3<T> &vk,
                                   const V3<T> &c) {
  using P = PolyT<T>;
  const T one(1), two(2);
  const P ww = PDot(ch.w, ch.w), D = P::Const(one) + ww;
  const PVecT<T> Nvk = (P::Const(one) - ww) * PConst(vk) + (two * PDot(ch.w, vk)) * ch.w + two * PCross(ch.w, PConst(vk));
  const PVecT<T> d = PCross(ch.u, PConst(c));
  const P base = PDot(Nvk, d);
  const PVecT<T> Dd = {D * d[0], D * d[1], D * d[2]};
  std::vector<P> out;
  for (const V3<T> &vj : pr.V) {
    P q = base - PDot(Dd, vj);
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
      for (const auto &p : WitnessPolys(st.pk, *chk, Cone(), st.pk.V[w.k], w.c)) ds.push_back(ToDense(p));
    } else {
      const auto &w = st.pd.W[wi];
      for (const auto &p : WitnessPolys(st.pd, chd, Cone(), st.pd.V[w.k], w.c)) ds.push_back(ToDense(p));
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
    for (const auto &p : WitnessPolys(st.pk, *chk, Cone(), st.pk.V[w.k], w.c)) ds.push_back(ToDenseK(p));
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
        double mx = -1e300;
        for (const auto &vj : st.pd.V) mx = std::max(mx, VDot(vj, d));
        const double v = (VDot(rv[st.pd.W[wi].k], d) - mx) / std::sqrt(VDot(d, d));
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
  std::string cap = "u0", only;
  int max_depth = 30, threads = 60;
  bool aniso = false, exact = true, mix = true;
  std::string debug_box;
  bool frame_only = false;
  double t0m = 0.25;
  int mcm = 1;
  std::string export_file;
  std::map<std::string, int> z_override;
  int ratio_z = 0, ratio_z_face = 0;
  double strong_scale = 2;
  Q mu0(41, 512);
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--cap") cap = next();
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
  st.t0m = t0m;
  st.mcm = mcm;
  st.z_override = z_override;
  const KNum s72{Q(0), Q(0), Q(1), Q(0)}, sqrt5{Q(0), Q(1), Q(0), Q(0)};
  if (cap == "u0") {
    // u0: the 2-fold vertex direction nearest (0.309, 0.425, 0.851); |v| = sqrt5.
    const V3<double> target{0.30901699437494740, 0.42532540417601999, 0.85065080835203999};
    int best = -1;
    double bd = -1;
    for (size_t j = 0; j < st.pd.V.size(); j++) {
      const double n = std::sqrt(VDot(st.pd.V[j], st.pd.V[j]));
      const double c = VDot(st.pd.V[j], target) / n;
      if (c > bd) { bd = c; best = j; }
    }
    CHECK(bd > 1 - 1e-12);
    const KNum inv5 = Inv(sqrt5);
    st.pk.x = VScale(inv5, st.pk.V[best]);
    CHECK(IsZero(VDot(st.pk.x, st.pk.x) - KNum(1))) << "|v| != sqrt5";
    st.half_turn = true;
  } else {
    // ux = (sin 72, (sqrt5 - 1)/4, 2) / sqrt5.
    const KNum inv5 = Inv(sqrt5);
    st.pk.x = VScale(inv5, V3<KNum>{s72, KNum{Q(-1, 4), Q(1, 4), Q(0), Q(0)}, KNum(2)});
    CHECK(IsZero(VDot(st.pk.x, st.pk.x) - KNum(1)));
    st.tie_cones = true;
  }
  // e1 = (x cross z) / |x cross z| (exact: |x cross z|^2 = 1 - x_z^2 must have a square root in K).
  const V3<KNum> xz = VCross(st.pk.x, V3<KNum>{KNum(0), KNum(0), KNum(1)});
  const KNum n2 = VDot(xz, xz);
  // Candidates for the norm: sqrt5 multiples and 1/(2 s) multiples.
  KNum nrm;
  bool found = false;
  for (const KNum &cand : {Inv(sqrt5), Inv(KNum(2) * s72)}) {
    if (IsZero(cand * cand - n2)) { nrm = cand; found = true; }
  }
  CHECK(found) << "|x cross z| not found in K";
  st.pk.e1 = VScale(Inv(nrm), xz);
  st.pk.e2 = VCross(st.pk.x, st.pk.e1);
  auto todbl = [](const V3<KNum> &v) { return V3<double>{ToDouble(v[0]), ToDouble(v[1]), ToDouble(v[2])}; };
  st.pd.x = todbl(st.pk.x);
  st.pd.e1 = todbl(st.pk.e1);
  st.pd.e2 = todbl(st.pk.e2);
  const std::vector<int> supp = SupportVertices(st.pd.V, st.pd.x);
  std::vector<std::vector<int>> nb(st.pd.V.size());
  for (auto &[a, b] : st.edges) { nb[a].push_back(b); nb[b].push_back(a); }
  for (int k : supp) {
    std::vector<int> others = nb[k];
    for (int m : supp) if (m != k && std::find(others.begin(), others.end(), m) == others.end()) others.push_back(m);
    std::vector<V3<KNum>> dirs;
    for (int m : others) {
      for (int sg : {1, -1}) {
        const V3<KNum> ck = sg > 0 ? VSub(st.pk.V[m], st.pk.V[k]) : VSub(st.pk.V[k], st.pk.V[m]);
        dirs.push_back(ck);
        st.pk.W.push_back({k, ck});
        st.pd.W.push_back({k, todbl(ck)});
      }
    }
    if (mix) {
      // Mixtures of angularly adjacent directions (the support direction d = x cross c
      // between two edges' normals): c1 + c2, c1 + 2 c2, 2 c1 + c2.
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
          st.pk.W.push_back({k, c});
          st.pd.W.push_back({k, todbl(c)});
        }
      }
    }
  }
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
          printf("witness %d (k %d): min over j of Bernstein lower %.3e (worst j %d)\n", wi, kk, v, wj);
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
    for (size_t i = 0; i < st.pk.V.size(); i++) fprintf(f, "vertex %zu %s\n", i, kv(st.pk.V[i]).c_str());
    for (size_t i = 0; i < st.pk.W.size(); i++)
      fprintf(f, "witness %zu %d %s\n", i, st.pk.W[i].k, kv(st.pk.W[i].c).c_str());
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
