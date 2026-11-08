// capcert-m12: capcert-neo (search/septopert-m18) generalized to M12 (septopert-m12-model.txt), --solid m12 (default) or m18.
// Notes: nopert229/out/bottleneck/neo/h12cap/REPORT.txt. M12 constants: t* = 4/19, arc end 5/14,
// flex (4-5t)/14 (A-E) and (4-14t)/5 (A-v4), blend (14-5)/14 v0 + 5/14 v5.
// Original header (M18):
// capcert-neo: cap and arc-cap certificates for the solid M18 (septopert-model.txt)
// near U = (2,2,-1)/3 and along the sub-arc u(phi) = sin phi (1,-2,-2)/3 + cos phi U,
// 0 < tan phi <= 11/32. Generalizes capcert-septopert-m12.cc (same Bernstein box
// subdivision); notes: nopert229/out/bottleneck/neo/capwork/REPORT.md.
//
// Apex frame (all vectors length 3): E1 = (-1,2,2), E2 = (2,-1,2), X = (2,2,-1).
// View u = X - a E1 - b E2 (tilt (a,b)). Cayley vector w = (wx E1 + wy E2 + wz X)/3,
// with relative tilt (d1,d2) = (2 wy, -2 wx) and in-plane spin wz = g.
//
// Witnesses are those of Pipeline/KCapCheck.lean: a reversed pair or a triple of
// directed vertex chords c_k, d_k = u x c_k, weights 1 or Cramer lambda_k =
// s (c_{k+1} x c_{k+2}).u >= 0, outer sets S_k proved to hold the maximum along d_k, and
// per outer tuple inner vertices i_k:
//   sum_k lambda_k (N(w) v_{i_k} - D(w) v_{j_k}) . d_k >= 0,
// divided by the chart's blow-up variables, by tensor Bernstein bounds. Polynomials are
// always built exactly; the default bounds them in plain double (feasibility); --exact accepts a
// bound only from exact rational Bernstein coefficients.
//
// Families (exact maps, domains, cover: capwork/REPORT.md):
//   --family U : u = X - a E1 - b E2, (a,b) = mu e (side), (d1,d2) = mu (s1,s2), g = mu^2 s3.
//   --family W : wedge along the arc, u = X - t E1 - b E2, b = t nu al,
//                w = (m1/2)(1,f(t),t) + (m2/2)(0,1,0) + m3 (0,0,1) in apex coordinates,
//                m1 = nu t s1, m2 = nu^2 t s2, m3 = nu^2 t^2 s3; --tmid: the mid chart at tan phi = 17/86.
// The final run is capwork/all.sh (arguments in REPORT.md).

#include <algorithm>
#include <array>
#include <atomic>
#include <cfenv>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <shared_mutex>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace {

constexpr int NV = 5;
using Exp = std::array<uint8_t, NV>;
using Q = BigRat;
using Box = std::array<std::pair<double, double>, NV>;

// ----- Polynomials over Q -----
struct Poly {
  std::map<Exp, Q> t;
  static Poly Const(const Q &c) { Poly p; if (!(c == Q(0))) p.t[Exp{}] = c; return p; }
  static Poly Var(int i) { Poly p; Exp e{}; e[i] = 1; p.t[e] = Q(1); return p; }
};
void Clean(Poly *p) {
  for (auto it = p->t.begin(); it != p->t.end();) {
    if (it->second == Q(0)) it = p->t.erase(it); else ++it;
  }
}
Poly operator+(const Poly &a, const Poly &b) {
  Poly r = a;
  for (const auto &[e, c] : b.t) {
    auto it = r.t.find(e);
    if (it == r.t.end()) r.t[e] = c; else it->second = it->second + c;
  }
  Clean(&r);
  return r;
}
Poly operator-(const Poly &a, const Poly &b) {
  Poly r = a;
  for (const auto &[e, c] : b.t) {
    auto it = r.t.find(e);
    if (it == r.t.end()) r.t[e] = Q(0) - c; else it->second = it->second - c;
  }
  Clean(&r);
  return r;
}
Poly operator*(const Poly &a, const Poly &b) {
  Poly r;
  for (const auto &[ea, ca] : a.t)
    for (const auto &[eb, cb] : b.t) {
      Exp e;
      for (int i = 0; i < NV; i++) e[i] = ea[i] + eb[i];
      auto it = r.t.find(e);
      if (it == r.t.end()) r.t[e] = ca * cb; else it->second = it->second + ca * cb;
    }
  Clean(&r);
  return r;
}
Poly operator*(const Q &s, const Poly &a) {
  Poly r;
  if (s == Q(0)) return r;
  for (const auto &[e, c] : a.t) r.t[e] = s * c;
  return r;
}
using V3 = std::array<Q, 3>;
using D3 = std::array<double, 3>;
using PVec = std::array<Poly, 3>;
PVec PConst(const V3 &v) { return {Poly::Const(v[0]), Poly::Const(v[1]), Poly::Const(v[2])}; }
PVec operator+(const PVec &a, const PVec &b) { return {a[0] + b[0], a[1] + b[1], a[2] + b[2]}; }
PVec operator*(const Poly &s, const PVec &a) { return {s * a[0], s * a[1], s * a[2]}; }
PVec operator*(const Q &s, const PVec &a) { return {s * a[0], s * a[1], s * a[2]}; }
Poly PDot(const PVec &a, const PVec &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
Poly PDot(const PVec &a, const V3 &c) { return c[0] * a[0] + c[1] * a[1] + c[2] * a[2]; }
PVec PCross(const PVec &a, const PVec &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
V3 VCross(const V3 &a, const V3 &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
V3 VSub(const V3 &a, const V3 &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
D3 ToD(const V3 &v) { return {v[0].ToDouble(), v[1].ToDouble(), v[2].ToDouble()}; }
double DDot(const D3 &a, const D3 &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
D3 DCross(const D3 &a, const D3 &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}

Poly DivideVar(const Poly &p, int i) {
  Poly q;
  int m = 1000;
  for (const auto &[e, c] : p.t) m = std::min(m, (int)e[i]);
  if (m == 1000 || m == 0) return p;
  for (const auto &[e, c] : p.t) { Exp f = e; f[i] -= m; q.t[f] = c; }
  return q;
}

// Sparse double copy for point evaluation.
struct Term { Exp e; double c; };
using DPoly = std::vector<Term>;
DPoly ToDP(const Poly &p) { DPoly d; for (const auto &[e, c] : p.t) d.push_back({e, c.ToDouble()}); return d; }
double EvalD(const DPoly &p, const double *x) {
  double s = 0;
  for (const auto &tm : p) {
    double v = tm.c;
    for (int i = 0; i < NV; i++) for (int k = 0; k < tm.e[i]; k++) v *= x[i];
    s += v;
  }
  return s;
}

// ----- Bernstein bounds -----
double Binom(int n, int k) {
  double r = 1;
  for (int i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return std::round(r);
}
// Dense coefficients (double), with the exact polynomial kept for the exact mode.
struct Dense {
  std::array<int, NV> deg{};
  std::vector<double> c;
  double scale = 1;  // max |c|
  Poly exact;
};
std::shared_ptr<Dense> MakeDense(const Poly &p) {
  auto d = std::make_shared<Dense>();
  for (const auto &[e, c] : p.t) for (int i = 0; i < NV; i++) d->deg[i] = std::max(d->deg[i], (int)e[i]);
  int n = 1;
  for (int i = 0; i < NV; i++) n *= d->deg[i] + 1;
  d->c.assign(n, 0.0);
  double sc = 0;
  for (const auto &[e, c] : p.t) {
    int idx = 0;
    for (int i = 0; i < NV; i++) idx = idx * (d->deg[i] + 1) + e[i];
    d->c[idx] = c.ToDouble();
    sc = std::max(sc, std::abs(d->c[idx]));
  }
  // Normalize: only the sign matters.
  if (sc > 0) { const double f = std::ldexp(1.0, -std::ilogb(sc)); for (double &x : d->c) x *= f; d->scale = 1; }
  d->exact = p;
  return d;
}
// Plain double lower bound (feasibility). The transform per axis: Bernstein coefficient I
// = sum_j M[I][j] mono_j, M from lo, h on that axis.
double BernsteinLowerD(const Dense &d, const Box &box) {
  thread_local std::vector<double> c, tmp;
  c = d.c;
  const int n = c.size();
  if (n == 0) return 0;
  std::array<int, NV> sz, stride;
  for (int i = 0; i < NV; i++) sz[i] = d.deg[i] + 1;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  for (int ax = 0; ax < NV; ax++) {
    const int D = d.deg[ax];
    if (D == 0) continue;
    const double lo = box[ax].first, h = box[ax].second - box[ax].first;
    double M[16][16];
    CHECK(D < 16);
    // x = lo + h y; mono in y: sum_j c_j (lo + h y)^j; coefficient of y^J = c_j C(j,J) lo^(j-J) h^J.
    // Bernstein: b_I = sum_J C(I,J)/C(D,J) a_J.
    double lop[17], hp[17];
    lop[0] = hp[0] = 1;
    for (int k = 1; k <= D; k++) { lop[k] = lop[k - 1] * lo; hp[k] = hp[k - 1] * h; }
    for (int I = 0; I <= D; I++)
      for (int j = 0; j <= D; j++) {
        double s = 0;
        for (int J = 0; J <= std::min(I, j); J++) s += Binom(I, J) / Binom(D, J) * Binom(j, J) * lop[j - J] * hp[J];
        M[I][j] = s;
      }
    const int st = stride[ax];
    double col[16];
    for (int base = 0; base < n; base++) {
      if ((base / st) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * st];
      for (int I = 0; I <= D; I++) {
        double s = 0;
        for (int j = 0; j <= D; j++) s += M[I][j] * col[j];
        c[base + I * st] = s;
      }
    }
  }
  double m = INFINITY;
  for (double x : c) m = std::min(m, x);
  return m;
}
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
// Exact tensor Bernstein lower bound, over Q.
Q ExactBernsteinLower(const Poly &p, const Box &box) {
  std::array<int, NV> deg{};
  for (const auto &[e, c] : p.t) for (int i = 0; i < NV; i++) deg[i] = std::max(deg[i], (int)e[i]);
  std::array<int, NV> sz, stride;
  for (int i = 0; i < NV; i++) sz[i] = deg[i] + 1;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  int n = 1;
  for (int i = 0; i < NV; i++) n *= sz[i];
  std::vector<Q> c(n, Q(0));
  for (const auto &[e, v] : p.t) {
    int idx = 0;
    for (int i = 0; i < NV; i++) idx += e[i] * stride[i];
    c[idx] = v;
  }
  for (int ax = 0; ax < NV; ax++) {
    const int D = deg[ax];
    if (D == 0) continue;
    const Q lo = DyadicRat(box[ax].first), h = DyadicRat(box[ax].second) - lo;
    std::vector<std::vector<Q>> M(D + 1, std::vector<Q>(D + 1, Q(0)));
    std::vector<Q> lop(D + 1, Q(1)), hp(D + 1, Q(1));
    for (int k = 1; k <= D; k++) { lop[k] = lop[k - 1] * lo; hp[k] = hp[k - 1] * h; }
    for (int I = 0; I <= D; I++)
      for (int j = 0; j <= D; j++) {
        Q s(0);
        for (int J = 0; J <= std::min(I, j); J++)
          s = s + Q((int64_t)Binom(I, J) * (int64_t)Binom(j, J)) / Q((int64_t)Binom(D, J)) * lop[j - J] * hp[J];
        M[I][j] = s;
      }
    const int st = stride[ax];
    std::vector<Q> col(D + 1, Q(0));
    for (int base = 0; base < n; base++) {
      if ((base / st) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * st];
      for (int I = 0; I <= D; I++) {
        Q s(0);
        for (int j = 0; j <= D; j++) if (!(col[j] == Q(0))) s = s + M[I][j] * col[j];
        c[base + I * st] = s;
      }
    }
  }
  Q m = c[0];
  for (const Q &x : c) if (x < m) m = x;
  return m;
}

// ----- The solid -----
struct Blend { int a, c; Q t; double td; };
constexpr int NI = 8;  // inner points at most
struct Solid {
  std::vector<Blend> blends;
  std::vector<V3> V;
  std::vector<D3> Vd;
  V3 E1, E2, X;
  Q k1{1, 3}, k2{1, 3}, k3{1, 3};  // Cayley w = k1 wx E1 + k2 wy E2 + k3 wz X (frames apex, axis)
  bool rotframe = false;  // frame P: w = wx W1 + wy W2 + wz W3 instead
  V3 W1, W2, W3;
};
std::string g_frame = "apex";
Q g_e1scale{1}, g_e2scale{1};
std::string g_w3;  // frame P: override W3 ("x,y,z" rationals)
int g_m3t = 2;
bool g_fpolar = false;  // wedge P: full polar charts on the faces al = +-1 (replaces Fe/cone)
bool g_polar = false;  // wedge P: polar outer pieces (ratio coordinate for the smaller of s1, s2)     // wedge P: m3 = nu^2 t^g_m3t s3  // view frame scales: E1 -> g_e1scale E1, E2 -> g_e2scale E2
std::string g_model = "septopert-m12-model.txt";
// Solid constants. Flex f = (fp - fq t)/fr per regime.
struct SolidConst { int scale; Q blend_t; int fp[2], fq[2], fr[2]; };
SolidConst g_sc{16, Q(5, 14), {4, 4}, {5, 14}, {14, 5}};
void SetSolid(const std::string &n) {
  if (n == "m18") { g_model = "../septopert-m18/septopert-m18-model.txt"; g_sc = SolidConst{32, Q(11, 32), {17, 17}, {22, 64}, {64, 22}}; }
  else CHECK(n == "m12") << n;
}
Poly FlexP(int regime, const Poly &t) {
  return Q(1, g_sc.fr[regime]) * (Poly::Const(Q(g_sc.fp[regime])) - Q(g_sc.fq[regime]) * t);
}
void LoadSolid(Solid *s) {
  std::ifstream in(g_model);
  CHECK(in.good()) << g_model;
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    if (tag != "rational_vertex") continue;
    int i;
    ss >> i;
    V3 v;
    for (int a = 0; a < 3; a++) {
      std::string t;
      CHECK(ss >> t);
      v[a] = Q(std::string_view(t)) * Q(g_sc.scale);  // integers; homogeneous
    }
    s->V.push_back(v);
    s->Vd.push_back(ToD(v));
  }
  CHECK(s->V.size() == 7);
  s->E1 = {Q(-1), Q(2), Q(2)};
  s->E2 = {Q(2), Q(-1), Q(2)};
  s->X = {Q(2), Q(2), Q(-1)};
  if (g_frame == "axis") {
    // The 3-fold axis view (1,1,1): u = X - a E1 - b E2, w = wx E1/2 + (2/3) wy E2 + wz X/3 (orthogonal frame).
    s->E1 = {Q(1), Q(-1), Q(0)};
    s->E2 = {Q(1, 2), Q(1, 2), Q(-1)};
    s->X = {Q(1), Q(1), Q(1)};
    s->k1 = Q(1, 2); s->k2 = Q(2, 3); s->k3 = Q(1, 3);
  } else if (g_frame == "P") {
    // P = (2,1,0): face 024 (normal N = (1,-2,1)) and face 162 edge-on. u = X - a E1 - b E2, E1 = -T/2 with T = (-1,2,5)
    // the tangent of face 024's circle (a = 2 s for u = P + s T), E2 = N (b > 0: v4 inside). Rotation frame: the
    // first-order flex lies in the plane perpendicular to (1,1,1): W1 = (7/10)(0,-1,1), W2 = (2/5)(2,-1,-1),
    // W3 = (4/7)(1,1,1) (orthogonal, lengths .990, .980, .990).
    s->X = {Q(2), Q(1), Q(0)};
    s->E1 = {Q(1, 2), Q(-1), Q(-5, 2)};
    s->E2 = {Q(1), Q(-2), Q(1)};
    s->rotframe = true;
    s->W1 = {Q(0), Q(-7, 10), Q(7, 10)};
    s->W2 = {Q(4, 5), Q(-2, 5), Q(-2, 5)};
    s->W3 = {Q(4, 7), Q(4, 7), Q(4, 7)};
    if (!g_w3.empty()) {
      std::stringstream ss(g_w3);
      std::string it;
      for (int i = 0; i < 3; i++) { CHECK(std::getline(ss, it, ',')); s->W3[i] = Q(std::string_view(it)); }
    }
  } else CHECK(g_frame == "apex") << g_frame;
  for (int i = 0; i < 3; i++) { s->E1[i] = g_e1scale * s->E1[i]; s->E2[i] = g_e2scale * s->E2[i]; }
  // v4 on segment A-E in the image at t* (A = v0, E = v5).
  s->blends.push_back({0, 5, g_sc.blend_t, g_sc.blend_t.ToDouble()});
}

// ----- Charts -----
struct Chart {
  std::string name;
  std::string id;  // the chart id in the export format (ArcCapDecode.lean); empty: not exported
  PVec u, w;
  std::vector<int> div;
  Box box;
  std::function<bool(const Box &)> prune;  // box lies in another chart
  std::array<DPoly, 3> ud, wd;
  void Finish() { for (int i = 0; i < 3; i++) { ud[i] = ToDP(u[i]); wd[i] = ToDP(w[i]); } }
};
PVec ApexView(const Solid &s, const Poly &a, const Poly &b) {
  return PConst(s.X) + (Q(0) - Q(1)) * (a * PConst(s.E1) + b * PConst(s.E2));
}
PVec ApexRot(const Solid &s, const Poly &wx, const Poly &wy, const Poly &wz) {
  if (s.rotframe) return wx * PConst(s.W1) + (wy * PConst(s.W2) + wz * PConst(s.W3));
  return s.k1 * (wx * PConst(s.E1)) + s.k2 * (wy * PConst(s.E2)) + s.k3 * (wz * PConst(s.X));
}

struct Params {
  // U cap.
  Q mu0{1, 16};
  double R = 2, S = 8, Rc = 0.5, Sc = 8;  // the identity cone covers |s1|,|s2| <= Rc, |s3| <= Sc
  std::vector<int> sides{0, 3};
  // Wedge.
  Q nu0{1, 4};
  double R1 = 3, R2 = 8, R3 = 16, Z = 16, Zc = 16, R2c = 8, R3c = 16;
  Q tlo{0}, thi{17, 86}, zl{0}, zh{0};
  bool tmid = false;
  double zmid = 8;
  int regime = 0;  // 0: A-E flex; 1: A-v4 flex
  int piece = 0;  // export: 0..3 = W0, Wm, W1, W2
  bool wedge_prune = false;  // U cap: skip boxes inside the wedge
  bool wp = false, wp_prune = false;  // wedge mode P: w = m1 W1 + m2 W2 + m3 W3, m1 = nu t s1, m2 = nu t s2, m3 = nu^2 t^2 s3 (no flex law)
};
Q QD(double x) { return DyadicRat(x); }

// U cap at P, side 0: the box lies in the P wedge (t = mu, al = tau/nu0, s1_w = -s2/(2 nu0), s2_w = s1/(2 nu0),
// s3_w = s3/nu0^2): |tau| <= nu0, |s2| <= 2 nu0 R1, |s1| <= 2 nu0 R2, |s3| <= nu0^2 R3, mu <= thi. Exact on box bounds.
// kind 0: Fe (s = p2, p3, p4); kind 2 + 2 ax + (sg < 0): cone(ax, sg), s_ax = sg rc_ax p2, s_fr = rc p2 p3, rc p2 p4.
std::function<bool(const Box &)> WpPrune(const Params &pr, int kind) {
  const Q n0 = pr.nu0, R1 = QD(pr.R1), R2 = QD(pr.R2), R3 = QD(pr.R3), thi = pr.thi;
  const Q rc[3] = {QD(pr.Rc), QD(pr.Rc), QD(pr.Sc)};
  return [=](const Box &b) {
    auto mx = [&](int i) { const Q l = Q::Abs(QD(b[i].first)), h = Q::Abs(QD(b[i].second)); return l < h ? h : l; };
    Q s[3];
    if (kind == 0) { s[0] = mx(2); s[1] = mx(3); s[2] = mx(4); }
    else {
      const int ax = (kind - 2) / 2;
      int fr[2], o = 0;
      for (int i = 0; i < 3; i++) if (i != ax) fr[o++] = i;
      s[ax] = rc[ax] * mx(2);
      s[fr[0]] = rc[fr[0]] * mx(2) * mx(3);
      s[fr[1]] = rc[fr[1]] * mx(2) * mx(4);
    }
    return !(n0 < mx(1)) && !(Q(2) * n0 * R1 < s[1]) && !(Q(2) * n0 * R2 < s[0]) && !(n0 * n0 * R3 < s[2]) && !(thi < QD(b[0].second));
  };
}

void AddUCharts(const Solid &so, const Params &pr, std::vector<Chart> *out) {
  const Poly mu = Poly::Var(0), tau = Poly::Var(1), P2 = Poly::Var(2), P3 = Poly::Var(3), P4 = Poly::Var(4);
  const double rng[3] = {pr.R, pr.R, pr.S};
  const double m0 = pr.mu0.ToDouble();
  for (int side : pr.sides) {
    auto mk = [&](const std::string &name, const Poly &e, const std::array<Poly, 3> &s, Box box,
                  std::vector<int> div, int kind, const std::string &idk) {
      Chart c;
      c.name = "U" + std::to_string(side) + ":" + name;
      c.id = "u " + std::to_string(side == 0 ? 1 : 0) + " " + idk;
      const Poly one = Poly::Const(Q(1)), me = mu * e;
      Poly a, b;
      switch (side) {
        case 0: a = me; b = me * tau; break;
        case 1: a = Q(-1) * me; b = me * tau; break;
        case 2: a = me * tau; b = me; break;
        default: a = me * tau; b = Q(-1) * me; break;
      }
      c.u = ApexView(so, a, b);
      const Poly d1 = mu * s[0], d2 = mu * s[1], g = (mu * mu) * s[2];
      c.w = ApexRot(so, Q(-1, 2) * d2, Q(1, 2) * d1, g);
      c.box = box;
      c.div = div;
      if (kind == 0 && side == 0 && pr.wp_prune) {
        auto wp = WpPrune(pr, 0);
        const double r0 = pr.Rc, r2 = pr.Sc;
        c.prune = [wp, r0, r2](const Box &b) {
          auto in = [](std::pair<double, double> v, double r) { return std::max(std::abs(v.first), std::abs(v.second)) <= r; };
          return (in(b[2], r0) && in(b[3], r0) && in(b[4], r2)) || wp(b);
        };
      } else if (kind == 0) {
        const double r0 = pr.Rc, r2 = pr.Sc;
        c.prune = [r0, r2](const Box &b) {
          auto in = [](std::pair<double, double> v, double r) { return std::max(std::abs(v.first), std::abs(v.second)) <= r; };
          return in(b[2], r0) && in(b[3], r0) && in(b[4], r2);
        };
      }
      out->push_back(std::move(c));
    };
    mk("Fe", Poly::Const(Q(1)), {P2, P3, P4},
       {{{0, m0}, {-1, 1}, {-rng[0], rng[0]}, {-rng[1], rng[1]}, {-rng[2], rng[2]}}}, {0}, 0, "0 0 0");
    for (int ax = 0; ax < 3; ax++)
      for (int sg : {1, -1}) {
        // face
        std::array<Poly, 3> s;
        int fr[2], o = 0;
        for (int i = 0; i < 3; i++) if (i != ax) fr[o++] = i;
        s[ax] = Poly::Const(QD(sg * rng[ax]));
        s[fr[0]] = P3;
        s[fr[1]] = P4;
        std::string nm = std::to_string(ax) + (sg > 0 ? "+" : "-");
        mk("face" + nm, P2, s, {{{0, m0}, {-1, 1}, {0, 1}, {-rng[fr[0]], rng[fr[0]]}, {-rng[fr[1]], rng[fr[1]]}}}, {0}, 1,
           "1 " + std::to_string(ax) + (sg > 0 ? " 1" : " 0"));
        // cone: s_i = p2 Range_i sigma_i
        std::array<Poly, 3> c;
        const double rc[3] = {pr.Rc, pr.Rc, pr.Sc};
        c[ax] = QD(sg * rc[ax]) * P2;
        c[fr[0]] = QD(rc[fr[0]]) * (P2 * P3);
        c[fr[1]] = QD(rc[fr[1]]) * (P2 * P4);
        mk("cone" + nm, Poly::Const(Q(1)), c, {{{0, m0}, {-1, 1}, {0, 1}, {-1, 1}, {-1, 1}}}, {0, 2}, 1,
           "2 " + std::to_string(ax) + (sg > 0 ? " 1" : " 0"));
        if (side == 0 && pr.wp_prune) out->back().prune = WpPrune(pr, 2 + ax * 2 + (sg > 0 ? 0 : 1));
        if (side == 0 && pr.wp_prune) {
          // face(ax, sg) of side 0 (a = mu e, e = p2): the box lies in the P wedge at nu = nu0 (t = mu e, al = tau/nu0,
          // s1_w = -s2/(2 nu0 e), s2_w = s1/(2 nu0 e), s3_w = s3/(nu0 e)^2) when, with e >= e_lo = p2's lower bound > 0,
          // |tau| <= nu0, |s2| <= 2 nu0 R1 e_lo, |s1| <= 2 nu0 R2 e_lo, |s3| <= nu0^2 R3 e_lo^2, mu_hi e_hi <= thi. Exact.
          Chart &fc = (*out)[out->size() - 2];
          const Q n0 = pr.nu0, R1 = QD(pr.R1), R2 = QD(pr.R2), R3 = QD(pr.R3), thi = pr.thi, rr = QD(sg * rng[ax]);
          const int axc = ax;
          fc.prune = [=](const Box &b) {
            auto mx = [&](int i) { const Q l = Q::Abs(QD(b[i].first)), h = Q::Abs(QD(b[i].second)); return l < h ? h : l; };
            const Q elo = QD(b[2].first), ehi = QD(b[2].second);
            if (!(Q(0) < elo)) return false;
            Q s[3];
            int fr[2], o = 0;
            for (int i = 0; i < 3; i++) if (i != axc) fr[o++] = i;
            s[axc] = Q::Abs(rr);
            s[fr[0]] = mx(3);
            s[fr[1]] = mx(4);
            return !(n0 < mx(1)) && !(Q(2) * n0 * R1 * elo < s[1]) && !(Q(2) * n0 * R2 * elo < s[0]) &&
                   !(n0 * n0 * R3 * elo * elo < s[2]) && !(thi < QD(b[0].second) * ehi);
          };
        }
        if (side == 0 && ax == 1 && sg == -1 && pr.wedge_prune) {
          // In the wedge: t = mu, nu al = tau, nu s1 = Rc t', nu^2 s2 = Rc t' (sigma1 - f), nu^2 s3 = t' (Sc sigma3 - Rc/2),
          // f = (17 - 22 mu)/64, so the pose is in the wedge's weighted cube when these are within nu0 (1, R1, R2, R3 scaled).
          // Exact over Q: this is Lean's ArcCap.wedgeBoxOk.
          const Q Rc = QD(pr.Rc), Sc = QD(pr.Sc), n0 = pr.nu0, R1 = QD(pr.R1), R2 = QD(pr.R2), R3 = QD(pr.R3);
          out->back().prune = [=](const Box &b) {
            auto lo = [&](int i) { return QD(b[i].first); };
            auto hi = [&](int i) { return QD(b[i].second); };
            auto f = [](const Q &m) { return Q(1, g_sc.fr[0]) * (Q(g_sc.fp[0]) - Q(g_sc.fq[0]) * m); };
            auto mx = [](const Q &x, const Q &y) { return Q::Abs(x) < Q::Abs(y) ? Q::Abs(y) : Q::Abs(x); };
            const Q tt = hi(2), dsig = mx(lo(3) - f(lo(0)), hi(3) - f(hi(0)));
            const Q half = Rc * Q(1, 2), dspin = mx(Sc * lo(4) - half, Sc * hi(4) - half);
            return !(n0 < mx(lo(1), hi(1))) && !(R1 * n0 < Rc * tt) && !(R2 * n0 * n0 < Rc * tt * dsig) &&
                   !(R3 * n0 * n0 < tt * dspin);
          };
        }
      }
  }
}

void AddWedgeCharts(const Solid &so, const Params &pr, std::vector<Chart> *out) {
  // Chart variables: nu (blow-up), p1 (t = tlo + (thi - tlo) p1), then the cube.
  //   view  u = X - t E1 - t nu al E2
  //   Cayley (apex frame)  w = (m1/2)(1, f(t), t) + (m2/2)(0,1,0) + m3 (0,0,1),
  //   m1 = nu t s1, m2 = nu^2 t s2, m3 = nu^2 t^2 s3.
  // Ratio split of s1: inner s1 = nu r (|r| <= Z), outer s1 = +-(Z nu + q).
  const Poly nu = Poly::Var(0), P1 = Poly::Var(1), P2 = Poly::Var(2), P3 = Poly::Var(3), P4 = Poly::Var(4);
  // t: tlo (1 + zl nu) + (thi (1 - zh nu) - tlo (1 + zl nu)) p1, or at a regime point tc (1 + nu p1).
  const Poly lo_t = pr.tlo * (Poly::Const(Q(1)) + pr.zl * nu), hi_t = pr.thi * (Poly::Const(Q(1)) - pr.zh * nu);
  const Poly t_lin = lo_t + (hi_t - lo_t) * P1;
  const double n0 = pr.nu0.ToDouble(), Z = pr.Z;
  const double R1 = pr.R1, R2 = pr.R2, R3 = pr.R3;
  auto mk = [&](const std::string &name, const Poly &al, const Poly &s1, const Poly &s2, const Poly &s3, Box box, bool cone, bool inner,
                const std::string &idk) {
    Chart c;
    c.name = "W" + std::to_string(pr.regime) + ":" + name;
    if (!idk.empty()) c.id = "w " + std::to_string(pr.piece) + " " + idk;
    // Mid chart at tc = tlo = 17/86 (v4 on line A-E exactly when t = tc (1 - b)):
    // b = (5/4) tc nu al, t = tc (1 - b + nu r), so that the offset of v4 from line A-E is proportional to r alone.
    const Poly b = pr.tmid ? (Q(5, 4) * pr.tlo) * (nu * al) : (t_lin * nu) * al;
    const Poly t = pr.tmid ? pr.tlo * (Poly::Const(Q(1)) - b + nu * P1) : t_lin;
    const Poly f = FlexP(pr.regime, t);
    c.u = ApexView(so, t, b);
    if (pr.wp) {
      const Poly m1 = (nu * t) * s1, m2 = (nu * t) * s2, m3 = (nu * nu) * (t * t) * s3;
      c.w = ApexRot(so, m1, m2, m3);
    } else {
    const Poly m1 = (nu * t) * s1, m2 = (nu * nu) * (t * s2), m3 = (nu * nu) * (t * t) * s3;
    const Poly wx = Q(1, 2) * m1, wy = Q(1, 2) * (m1 * f + m2), wz = Q(1, 2) * (m1 * t) + m3;
    c.w = ApexRot(so, wx, wy, wz);
    }
    c.box = box;
    c.div = {0};  // only variables >= 0 on the chart: nu, p1 unless p1 is the signed r of the mid chart, the cone radius
    if (!pr.tmid) c.div.push_back(1);
    if (cone) c.div.push_back(2);
    if (inner) {
      const double r0 = pr.Zc, r1 = pr.R2c, r2 = pr.R3c;
      c.prune = [r0, r1, r2](const Box &b) {
        auto in = [](std::pair<double, double> v, double r) { return std::max(std::abs(v.first), std::abs(v.second)) <= r; };
        return in(b[2], r0) && in(b[3], r1) && in(b[4], r2);
      };
    }
    out->push_back(std::move(c));
  };
  const std::pair<double, double> NU{0, n0}, T = pr.tmid ? std::pair<double, double>{-pr.zmid, pr.zmid} : std::pair<double, double>{0, 1};
  const Q Zq = QD(Z);
  for (int al : {1, -1}) {
    const Poly A = Poly::Const(Q(al));
    const std::string as = al > 0 ? "+" : "-", ab = al > 0 ? "1" : "0";
    mk("FeI" + as, A, nu * P2, P3, P4, {{NU, T, {-Z, Z}, {-R2, R2}, {-R3, R3}}}, false, true, "");
    mk("FeP" + as, A, Zq * nu + P2, P3, P4, {{NU, T, {0, R1}, {-R2, R2}, {-R3, R3}}}, false, false, "0 " + ab + " 1 0");
    mk("FeM" + as, A, Q(-1) * (Zq * nu + P2), P3, P4, {{NU, T, {0, R1}, {-R2, R2}, {-R3, R3}}}, false, false, "0 " + ab + " 0 0");
    const double rc[3] = {pr.Zc, pr.R2c, pr.R3c};
    for (int ax = 0; ax < 3; ax++)
      for (int sg : {1, -1}) {
        int fr[2], o = 0;
        for (int i = 0; i < 3; i++) if (i != ax) fr[o++] = i;
        Poly c[3];
        c[ax] = QD(sg * rc[ax]) * P2;
        c[fr[0]] = QD(rc[fr[0]]) * (P2 * P3);
        c[fr[1]] = QD(rc[fr[1]]) * (P2 * P4);
        mk("cone" + as + std::to_string(ax) + (sg > 0 ? "+" : "-"), A, nu * c[0], c[1], c[2], {{NU, T, {0, 1}, {-1, 1}, {-1, 1}}}, true, false,
           "1 " + ab + " " + std::to_string(ax) + (sg > 0 ? " 1" : " 0"));
      }
  }
  // Faces: al = p2 in [-1,1].
  for (int sg : {1, -1}) {
    const std::string ss = sg > 0 ? "+" : "-", sb = sg > 0 ? "1" : "0";
    const Q sq(sg);
    mk("face0" + ss, P2, Poly::Const(sq * QD(R1)), P3, P4, {{NU, T, {-1, 1}, {-R2, R2}, {-R3, R3}}}, false, false, "2 " + sb + " 0 0");
    // s2 = sg R2; s1 from p3, s3 = p4.
    const Poly S2 = Poly::Const(QD(sg * R2)), S3 = Poly::Const(QD(sg * R3));
    mk("face1I" + ss, P2, nu * P3, S2, P4, {{NU, T, {-1, 1}, {-Z, Z}, {-R3, R3}}}, false, false, "3 " + sb + " 0 0");
    mk("face1P" + ss, P2, Zq * nu + P3, S2, P4, {{NU, T, {-1, 1}, {0, R1}, {-R3, R3}}}, false, false, "3 " + sb + " 1 0");
    mk("face1M" + ss, P2, Q(-1) * (Zq * nu + P3), S2, P4, {{NU, T, {-1, 1}, {0, R1}, {-R3, R3}}}, false, false, "3 " + sb + " 2 0");
    mk("face2I" + ss, P2, nu * P3, P4, S3, {{NU, T, {-1, 1}, {-Z, Z}, {-R2, R2}}}, false, false, "4 " + sb + " 0 0");
    mk("face2P" + ss, P2, Zq * nu + P3, P4, S3, {{NU, T, {-1, 1}, {0, R1}, {-R2, R2}}}, false, false, "4 " + sb + " 1 0");
    mk("face2M" + ss, P2, Q(-1) * (Zq * nu + P3), P4, S3, {{NU, T, {-1, 1}, {0, R1}, {-R2, R2}}}, false, false, "4 " + sb + " 2 0");
  }
}

// Wedge along face 024's circle from P (frame P): u = X - t E1 - b E2, b = t nu al, t = thi p1;
// w = m1 W1 + m2 W2 + m3 W3, m1 = nu t s1, m2 = nu t s2, m3 = nu^2 t^2 s3 (the flex plane W1, W2 is first order).
// Cube (al; s1, s2, s3), weights (1; 1, 1, 2), ranges (1; R1, R2, R3). Ratio split of (s1, s2) at Z nu:
//   al = +-1: Fe1P/M: s1 = +-(Z nu + p2), s2 = p3;  Fe2P/M: s1 = nu p2 (|p2| <= Z), s2 = +-(Z nu + p3);  s3 = p4;
//             cone(ax,sg): (r1, r2, s3) = p2 (Z, Z, R3) sigma, s1 = nu r1, s2 = nu r2 (sigma on the face (ax,sg)).
//   faces: al = p2;  face0: s1 = +-R1;  face1: s2 = +-R2;  face2: s3 = +-R3 with (s1, s2) split I/1P/1M/2P/2M.
void AddWedgeChartsP(const Solid &so, const Params &pr, std::vector<Chart> *out) {
  const Poly nu = Poly::Var(0), P1 = Poly::Var(1), P2 = Poly::Var(2), P3 = Poly::Var(3), P4 = Poly::Var(4);
  const Poly t = Poly::Const(pr.tlo) + (pr.thi - pr.tlo) * P1;
  const double n0 = pr.nu0.ToDouble(), Z = pr.Z, R1 = pr.R1, R2 = pr.R2, R3 = pr.R3;
  const Q Zq = QD(Z);
  auto mk = [&](const std::string &name, const Poly &al, const Poly &s1, const Poly &s2, const Poly &s3, Box box, bool cone) {
    Chart c;
    c.name = "WP:" + name;
    c.u = ApexView(so, t, (t * nu) * al);
    c.w = ApexRot(so, (nu * t) * s1, (nu * t) * s2, (nu * nu) * (g_m3t == 2 ? t * t : t) * s3);
    c.box = box;
    c.div = {0};
    if (pr.tlo == Q(0)) c.div.push_back(1);
    if (cone) c.div.push_back(2);
    out->push_back(std::move(c));
  };
  const std::pair<double, double> NU{0, n0}, T{0, 1};
  for (int al : {1, -1}) {
    const Poly A = Poly::Const(Q(al));
    const std::string as = al > 0 ? "+" : "-";
    if (g_fpolar) {
      // Full polar on the face al = +-1 (task 3 continued): the flex-stress margin there is homogeneous of degree 1
      // in (s1, s2, s3) jointly (branches +-c s3 + B.s), so s3 scales with the in-plane part. Dominant axis k, sign sg:
      // s_k = sg R_k rho, s_l = R_l rho q_l (l != k), rho = p2 in [0,1], q = p3, p4 in [-1,1]. Divide by nu, t, rho.
      const double Rk[3] = {R1, R2, R3};
      for (int k = 0; k < 3; k++)
        for (int sg : {1, -1}) {
          Poly c[3];
          int o = 0;
          const Poly Pq[2] = {P3, P4};
          for (int l = 0; l < 3; l++) c[l] = (l == k) ? QD(sg * Rk[l]) * P2 : QD(Rk[l]) * (P2 * Pq[o++]);
          mk("Fp" + as + std::to_string(k) + (sg > 0 ? "+" : "-"), A, c[0], c[1], c[2], {{NU, T, {0, 1}, {-1, 1}, {-1, 1}}}, true);
        }
      continue;
    }
    if (g_polar) {
      // Polar outer pieces: the larger of |s1|, |s2| is Z nu + p2, the other its multiple p3 in [-1, 1].
      const Poly S1p = Zq * nu + P2, S1m = Q(-1) * (Zq * nu + P2);
      mk("Fe1P" + as, A, S1p, S1p * P3, P4, {{NU, T, {0, R1}, {-1, 1}, {-R3, R3}}}, false);
      mk("Fe1M" + as, A, S1m, S1m * P3, P4, {{NU, T, {0, R1}, {-1, 1}, {-R3, R3}}}, false);
      mk("Fe2P" + as, A, S1p * P3, S1p, P4, {{NU, T, {0, R2}, {-1, 1}, {-R3, R3}}}, false);
      mk("Fe2M" + as, A, S1m * P3, S1m, P4, {{NU, T, {0, R2}, {-1, 1}, {-R3, R3}}}, false);
    } else {
    mk("Fe1P" + as, A, Zq * nu + P2, P3, P4, {{NU, T, {0, R1}, {-R2, R2}, {-R3, R3}}}, false);
    mk("Fe1M" + as, A, Q(-1) * (Zq * nu + P2), P3, P4, {{NU, T, {0, R1}, {-R2, R2}, {-R3, R3}}}, false);
    mk("Fe2P" + as, A, nu * P2, Zq * nu + P3, P4, {{NU, T, {-Z, Z}, {0, R2}, {-R3, R3}}}, false);
    mk("Fe2M" + as, A, nu * P2, Q(-1) * (Zq * nu + P3), P4, {{NU, T, {-Z, Z}, {0, R2}, {-R3, R3}}}, false);
    }
    const double rc[3] = {Z, Z, R3};
    for (int ax = 0; ax < 3; ax++)
      for (int sg : {1, -1}) {
        int fr[2], o = 0;
        for (int i = 0; i < 3; i++) if (i != ax) fr[o++] = i;
        Poly c[3];
        c[ax] = QD(sg * rc[ax]) * P2;
        c[fr[0]] = QD(rc[fr[0]]) * (P2 * P3);
        c[fr[1]] = QD(rc[fr[1]]) * (P2 * P4);
        mk("cone" + as + std::to_string(ax) + (sg > 0 ? "+" : "-"), A, nu * c[0], nu * c[1], c[2], {{NU, T, {0, 1}, {-1, 1}, {-1, 1}}}, true);
      }
  }
  for (int sg : {1, -1}) {
    const std::string ss = sg > 0 ? "+" : "-";
    const Q sq(sg);
    mk("face0" + ss, P2, Poly::Const(sq * QD(R1)), P3, P4, {{NU, T, {-1, 1}, {-R2, R2}, {-R3, R3}}}, false);
    mk("face1" + ss, P2, P3, Poly::Const(sq * QD(R2)), P4, {{NU, T, {-1, 1}, {-R1, R1}, {-R3, R3}}}, false);
    const Poly S3 = Poly::Const(sq * QD(R3));
    mk("face2I" + ss, P2, nu * P3, nu * P4, S3, {{NU, T, {-1, 1}, {-Z, Z}, {-Z, Z}}}, false);
    if (g_polar) {
      const Poly Sp = Zq * nu + P3, Sm = Q(-1) * (Zq * nu + P3);
      mk("face2_1P" + ss, P2, Sp, Sp * P4, S3, {{NU, T, {-1, 1}, {0, R1}, {-1, 1}}}, false);
      mk("face2_1M" + ss, P2, Sm, Sm * P4, S3, {{NU, T, {-1, 1}, {0, R1}, {-1, 1}}}, false);
      mk("face2_2P" + ss, P2, Sp * P4, Sp, S3, {{NU, T, {-1, 1}, {0, R2}, {-1, 1}}}, false);
      mk("face2_2M" + ss, P2, Sm * P4, Sm, S3, {{NU, T, {-1, 1}, {0, R2}, {-1, 1}}}, false);
    } else {
    mk("face2_1P" + ss, P2, Zq * nu + P3, P4, S3, {{NU, T, {-1, 1}, {0, R1}, {-R2, R2}}}, false);
    mk("face2_1M" + ss, P2, Q(-1) * (Zq * nu + P3), P4, S3, {{NU, T, {-1, 1}, {0, R1}, {-R2, R2}}}, false);
    mk("face2_2P" + ss, P2, nu * P3, Zq * nu + P4, S3, {{NU, T, {-1, 1}, {-Z, Z}, {0, R2}}}, false);
    mk("face2_2M" + ss, P2, nu * P3, Q(-1) * (Zq * nu + P4), S3, {{NU, T, {-1, 1}, {-Z, Z}, {0, R2}}}, false);
    }
  }
}

// Independent check: the clearance deficit of the pose (LP over the outer hull's edges): > 0 means no passage.
double ClearDeficit(const std::vector<D3> &V, const D3 &u, const D3 &w) {
  auto nrm = [](D3 a) { const double n = std::sqrt(DDot(a, a)); return D3{a[0] / n, a[1] / n, a[2] / n}; };
  const D3 un = nrm(u), h1 = nrm(DCross(un, D3{0.3, 1, 0.1})), h2 = DCross(un, h1);
  const int n = V.size();
  std::vector<std::array<double, 2>> po(n), pi(n);
  const double W = DDot(w, w);
  for (int i = 0; i < n; i++) {
    const D3 c = DCross(w, V[i]);
    const double wv = DDot(w, V[i]);
    D3 r;
    for (int a = 0; a < 3; a++) r[a] = ((1 - W) * V[i][a] + 2 * w[a] * wv + 2 * c[a]) / (1 + W);
    po[i] = {DDot(V[i], h1), DDot(V[i], h2)};
    pi[i] = {DDot(r, h1), DDot(r, h2)};
  }
  std::vector<int> idx(n), H;
  for (int i = 0; i < n; i++) idx[i] = i;
  std::sort(idx.begin(), idx.end(), [&](int a, int b) { return po[a] < po[b]; });
  auto cr = [&](int o, int a, int b) { return (po[a][0] - po[o][0]) * (po[b][1] - po[o][1]) - (po[a][1] - po[o][1]) * (po[b][0] - po[o][0]); };
  for (int pass = 0; pass < 2; pass++) {
    const size_t st = H.size();
    for (int i : idx) { while (H.size() >= st + 2 && cr(H[H.size() - 2], H.back(), i) <= 0) H.pop_back(); H.push_back(i); }
    H.pop_back();
    std::reverse(idx.begin(), idx.end());
  }
  const int m = H.size();
  std::vector<std::array<double, 3>> E;
  for (int e = 0; e < m; e++) {
    const auto p = po[H[e]], q = po[H[(e + 1) % m]];
    double nx = q[1] - p[1], ny = -(q[0] - p[0]);
    const double L = std::hypot(nx, ny);
    nx /= L; ny /= L;
    const double h = nx * p[0] + ny * p[1];
    double hi = -1e300;
    for (int i = 0; i < n; i++) hi = std::max(hi, nx * pi[i][0] + ny * pi[i][1]);
    E.push_back({nx, ny, hi - h});
  }
  double best = -1e300;
  for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) for (int c = b + 1; c < m; c++) {
    const double l0 = E[b][0] * E[c][1] - E[b][1] * E[c][0], l1 = E[c][0] * E[a][1] - E[c][1] * E[a][0], l2 = E[a][0] * E[b][1] - E[a][1] * E[b][0];
    if ((l0 >= 0 && l1 >= 0 && l2 >= 0) || (l0 <= 0 && l1 <= 0 && l2 <= 0)) {
      const double s = l0 + l1 + l2;
      if (std::abs(s) < 1e-13) continue;
      best = std::max(best, (l0 * E[a][2] + l1 * E[b][2] + l2 * E[c][2]) / s);
    }
  }
  return best;
}

// ----- Witnesses -----
struct Chord { int a, b; V3 c; D3 cd; double len = 1; };  // directed: c = v_b - v_a
struct Wit {
  int n;          // 2 or 3
  int ch[3];      // directed chord indices
  int s;          // Cramer sign (triples)
  D3 cr[3];       // s (c_{k+1} x c_{k+2}) (double)
};
struct Pool {
  std::vector<Chord> chords;
  std::vector<Wit> wits;
};
void MakePool(const Solid &so, Pool *p) {
  const int n = so.V.size();
  for (int a = 0; a < n; a++)
    for (int b = 0; b < n; b++)
      if (a != b) {
        Chord c{a, b, VSub(so.V[b], so.V[a]), {}};
        c.cd = ToD(c.c);
        c.len = std::sqrt(DDot(c.cd, c.cd));
        p->chords.push_back(c);
      }
  const int m = p->chords.size();
  auto idx = [&](int a, int b) { for (int i = 0; i < m; i++) if (p->chords[i].a == a && p->chords[i].b == b) return i; return -1; };
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++) {
      Wit w{2, {idx(a, b), idx(b, a), -1}, 1, {}};
      p->wits.push_back(w);
    }
  // Triples of chords (distinct undirected; directed both ways); s = +-1. Each unordered triple once.
  for (int i = 0; i < m; i++)
    for (int j = i + 1; j < m; j++)
      for (int k = j + 1; k < m; k++) {
        const Chord &A = p->chords[i], &B = p->chords[j], &C = p->chords[k];
        auto same = [](const Chord &x, const Chord &y) { return x.a == y.b && x.b == y.a; };
        if (same(A, B) || same(A, C) || same(B, C)) continue;
        for (int s : {1, -1}) {
          Wit w{3, {i, j, k}, s, {}};
          const D3 *cc[3] = {&A.cd, &B.cd, &C.cd};
          for (int q = 0; q < 3; q++) {
            D3 x = DCross(*cc[(q + 1) % 3], *cc[(q + 2) % 3]);
            w.cr[q] = {s * x[0], s * x[1], s * x[2]};
          }
          p->wits.push_back(w);
        }
      }
}

struct Stats { std::atomic<int64_t> selfbad{0}, exact_calls{0}; std::atomic<int64_t> ok{0}, pruned{0}, failed{0}, tries{0}, bern{0}; std::atomic<int64_t> depth_hist[64]; };

FILE *g_leaflog = nullptr;
int g_try = 12, g_topk = 300;
size_t g_combos = 6;
FILE *g_faillog = nullptr;
bool g_exact = false;

struct Certifier {
  const Solid &so;
  const Pool &pool;
  const Chart &ch;
  int max_depth;
  int64_t max_fail;
  Stats st;
  std::mutex mu;
  std::shared_mutex cache_mu;
  // Chart-level witness subset (balanced somewhere in the chart).
  std::vector<int> active;
  std::map<std::tuple<int, int, int>, std::shared_ptr<Dense>> dom;  // (chord, head, j)
  std::map<int, std::shared_ptr<Dense>> lamc;  // (witness*3+k)
  std::map<int, std::shared_ptr<Dense>> posc;
  std::map<std::array<int, 7>, std::shared_ptr<Dense>> tup;  // witness, i0..2, j0..2
  struct WTerms { PVec Ls[3], d[3]; std::map<int, Poly> A[3], B[3]; std::mutex m; };
  std::map<int, std::unique_ptr<WTerms>> wt;
  Poly ww, Dw;
  std::vector<PVec> Nv;  // inner numerators: vertices, then blends
  std::vector<std::string> fail_boxes;
  std::vector<std::string> *log = nullptr;

  Certifier(const Solid &s, const Pool &p, const Chart &c, int md, int64_t mf) : so(s), pool(p), ch(c), max_depth(md), max_fail(mf) {
    for (auto &x : st.depth_hist) x = 0;
    ww = PDot(ch.w, ch.w);
    Dw = Poly::Const(Q(1)) + ww;
    const Poly one_m = Poly::Const(Q(1)) - ww;
    for (int i = 0; i < 7; i++) {
      const PVec v = PConst(so.V[i]);
      Nv.push_back(one_m * v + (Q(2) * PDot(ch.w, so.V[i])) * ch.w + Q(2) * PCross(ch.w, v));
    }
    for (const Blend &b : so.blends) Nv.push_back((Q(1) - b.t) * Nv[b.a] + b.t * Nv[b.c]);
    SelectActive();
  }

  // Point data.
  struct PD {
    D3 u; double g[64], dn[64]; double hi[64][NI], ho[64][7]; int ai[64]; double D;
  };
  void Point(const double *x, PD *o) const {
    D3 u, w;
    for (int a = 0; a < 3; a++) { u[a] = EvalD(ch.ud[a], x); w[a] = EvalD(ch.wd[a], x); }
    o->u = u;
    const double W = DDot(w, w), Dw_ = 1 + W;
    o->D = Dw_;
    D3 rv[7];
    for (int k = 0; k < 7; k++) {
      const D3 &v = so.Vd[k];
      const D3 c = DCross(w, v);
      const double wv = DDot(w, v);
      for (int a = 0; a < 3; a++) rv[k][a] = ((1 - W) * v[a] + 2 * w[a] * wv + 2 * c[a]) / Dw_;
    }
    const int m = pool.chords.size();
    for (int c = 0; c < m; c++) {
      const D3 d = DCross(u, pool.chords[c].cd);
      o->dn[c] = std::sqrt(DDot(d, d));
      double mo = -1e300, mi = -1e300;
      for (int k = 0; k < 7; k++) {
        const double a = DDot(so.Vd[k], d), b = DDot(rv[k], d);
        o->ho[c][k] = a;
        o->hi[c][k] = b;
        mo = std::max(mo, a);
        mi = std::max(mi, b);
      }
      int q = 7;
      for (const Blend &bl : so.blends) { o->hi[c][q] = (1 - bl.td) * o->hi[c][bl.a] + bl.td * o->hi[c][bl.c]; q++; }
      o->g[c] = mi - mo;
    }
  }
  // lambda_k at u.
  void Lams(const Wit &w, const D3 &u, double *l) const {
    if (w.n == 2) { l[0] = l[1] = 1; return; }
    for (int k = 0; k < 3; k++) l[k] = DDot(w.cr[k], u);
  }
  double Value(const Wit &w, const PD &p) const {
    double l[3];
    Lams(w, p.u, l);
    double num = 0, den = 0;
    for (int k = 0; k < w.n; k++) {
      if (l[k] < 0) return -INFINITY;
      num += l[k] * p.g[w.ch[k]];
      den += l[k] * pool.chords[w.ch[k]].len;
    }
    if (den <= 0) return -INFINITY;
    return num / den;
  }
  void SelectActive() {
    // A witness is active if lambda >= 0 at some sample of the chart.
    std::vector<char> on(pool.wits.size(), 0);
    uint64_t rs = 88172645463325252ULL;
    auto rnd = [&]() { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (rs >> 11) * (1.0 / 9007199254740992.0); };
    for (int it = 0; it < 400; it++) {
      double x[NV];
      for (int i = 0; i < NV; i++) x[i] = ch.box[i].first + (ch.box[i].second - ch.box[i].first) * rnd();
      D3 u;
      for (int a = 0; a < 3; a++) u[a] = EvalD(ch.ud[a], x);
      for (size_t w = 0; w < pool.wits.size(); w++) {
        if (on[w]) continue;
        double l[3];
        Lams(pool.wits[w], u, l);
        bool ok = true;
        for (int k = 0; k < pool.wits[w].n; k++) ok = ok && l[k] >= 0;
        if (ok) on[w] = 1;
      }
    }
    for (size_t w = 0; w < on.size(); w++) if (on[w]) active.push_back(w);
  }

  WTerms &Terms(int wi) {
    std::lock_guard<std::mutex> l(mu);
    auto it = wt.find(wi);
    if (it != wt.end()) return *it->second;
    auto t = std::make_unique<WTerms>();
    const Wit &w = pool.wits[wi];
    for (int k = 0; k < w.n; k++) t->d[k] = PCross(ch.u, PConst(pool.chords[w.ch[k]].c));
    for (int k = 0; k < w.n; k++) {
      if (w.n == 2) t->Ls[k] = t->d[k];
      else {
        const V3 cr = VCross(pool.chords[w.ch[(k + 1) % 3]].c, pool.chords[w.ch[(k + 2) % 3]].c);
        const Poly lam = Q(w.s) * PDot(ch.u, cr);
        t->Ls[k] = lam * t->d[k];
      }
    }
    return *(wt[wi] = std::move(t));
  }
  const Poly &TA(WTerms &t, int k, int i) {
    std::lock_guard<std::mutex> l(t.m);
    auto it = t.A[k].find(i);
    if (it != t.A[k].end()) return it->second;
    return t.A[k][i] = PDot(Nv[i], t.Ls[k]);
  }
  const Poly &TB(WTerms &t, int k, int j) {
    std::lock_guard<std::mutex> l(t.m);
    auto it = t.B[k].find(j);
    if (it != t.B[k].end()) return it->second;
    return t.B[k][j] = Dw * PDot(t.Ls[k], so.V[j]);
  }
  std::shared_ptr<Dense> LamD(int wi, int k) {
    const int key = wi * 3 + k;
    { std::shared_lock l(cache_mu); auto it = lamc.find(key); if (it != lamc.end()) return it->second; }
    const Wit &w = pool.wits[wi];
    const V3 cr = VCross(pool.chords[w.ch[(k + 1) % 3]].c, pool.chords[w.ch[(k + 2) % 3]].c);
    auto d = MakeDense(Q(w.s) * PDot(ch.u, cr));
    std::unique_lock l(cache_mu);
    return lamc[key] = d;
  }
  std::shared_ptr<Dense> DomD(int c, int h, int j) {
    const auto key = std::make_tuple(c, h, j);
    { std::shared_lock l(cache_mu); auto it = dom.find(key); if (it != dom.end()) return it->second; }
    auto d = MakeDense(PDot(PCross(ch.u, PConst(pool.chords[c].c)), VSub(so.V[h], so.V[j])));
    std::unique_lock l(cache_mu);
    return dom[key] = d;
  }
  std::shared_ptr<Dense> TupD(int wi, const int *i, const int *j) {
    std::array<int, 7> key{wi, i[0], i[1], i[2], j[0], j[1], j[2]};
    { std::shared_lock l(cache_mu); auto it = tup.find(key); if (it != tup.end()) return it->second; }
    WTerms &t = Terms(wi);
    const Wit &w = pool.wits[wi];
    Poly p;
    for (int k = 0; k < w.n; k++) p = p + (TA(t, k, i[k]) - TB(t, k, j[k]));
    for (int v : ch.div) p = DivideVar(p, v);
    auto d = MakeDense(p);
    std::unique_lock l(cache_mu);
    return tup[key] = d;
  }

  bool NonNeg(const Dense &d, const Box &box) {
    st.bern++;
    if (d.c.empty()) return true;
    const double lb = BernsteinLowerD(d, box);
    if (!g_exact) return lb >= -1e-11;
    if (lb < -1e-9) return false;
    st.exact_calls++;
    return !(ExactBernsteinLower(d.exact, box) < Q(0));  // every accepted bound is exact over Q
  }
  bool Positive(const Dense &d, const Box &box) {
    if (d.c.empty()) return false;
    const double lb = BernsteinLowerD(d, box);
    if (!g_exact) return lb > 1e-11;
    if (lb < -1e-9) return false;
    st.exact_calls++;
    return Q(0) < ExactBernsteinLower(d.exact, box);
  }
  // Lean's posOn: sum_k lambda_k d_k . d_k > 0 on the box.
  std::shared_ptr<Dense> PosD(int wi) {
    { std::shared_lock l(cache_mu); auto it = posc.find(wi); if (it != posc.end()) return it->second; }
    WTerms &t = Terms(wi);
    Poly p;
    for (int k = 0; k < pool.wits[wi].n; k++) p = p + PDot(t.Ls[k], t.d[k]);
    auto d = MakeDense(p);
    std::unique_lock l(cache_mu);
    return posc[wi] = d;
  }

  std::string WitName(int wi) const {
    static const char *NM[7] = {"A", "B", "C", "v3", "v4", "E", "O"};
    const Wit &w = pool.wits[wi];
    std::string r;
    for (int k = 0; k < w.n; k++) r += std::string(NM[pool.chords[w.ch[k]].a]) + ">" + NM[pool.chords[w.ch[k]].b] + " ";
    return r + (w.s > 0 ? "s+" : "s-");
  }
  // Debug: the best witnesses at a box: their value at the sample points, why Try fails.
  void Debug(const Box &box) {
    double c[NV];
    for (int i = 0; i < NV; i++) c[i] = 0.5 * (box[i].first + box[i].second);
    PD p0;
    std::vector<PD> pts(2 * NV + 1);
    Point(c, &pts[0]);
    for (int i = 0; i < NV; i++) {
      double x[NV];
      std::copy(c, c + NV, x);
      const double h = 0.48 * (box[i].second - box[i].first);
      x[i] = c[i] - h; Point(x, &pts[1 + 2 * i]);
      x[i] = c[i] + h; Point(x, &pts[2 + 2 * i]);
    }
    D3 u, w;
    for (int a = 0; a < 3; a++) { u[a] = EvalD(ch.ud[a], c); w[a] = EvalD(ch.wd[a], c); }
    printf("center u %.6g %.6g %.6g w %.6g %.6g %.6g\n", u[0], u[1], u[2], w[0], w[1], w[2]);
    std::vector<std::pair<double, int>> sc;
    for (int wi : active) sc.push_back({Value(pool.wits[wi], pts[0]), wi});
    std::sort(sc.rbegin(), sc.rend());
    for (int r = 0; r < 10 && r < (int)sc.size(); r++) {
      const int wi = sc[r].second;
      double mn = 1e300;
      for (auto &p : pts) mn = std::min(mn, Value(pool.wits[wi], p));
      verbose = r < 4;
      printf("  %-24s center %.4g min-over-pts %.4g\n", WitName(wi).c_str(), sc[r].first, mn);
      printf("   try %d\n", (int)Try(wi, box, pts));
    }
  }

  // Tries witness wi on the box. Sample points' data in pts.
  bool verbose = false;
  static inline thread_local std::string last_leaf;
  bool Try(int wi, const Box &box, const std::vector<PD> &pts) {
    const Wit &w = pool.wits[wi];
    st.tries++;
    if (w.n == 3)
      for (int k = 0; k < 3; k++) if (!NonNeg(*LamD(wi, k), box)) { if (verbose) printf("      lam %d negative\n", k); return false; }
    if (!Positive(*PosD(wi), box)) { if (verbose) printf("      posOn fails\n"); return false; }
    // Outer sets.
    std::vector<int> S[3];
    for (int k = 0; k < w.n; k++) {
      const int c = w.ch[k];
      std::array<int, 7> cnt{};
      for (const PD &p : pts) {
        int b = 0;
        for (int v = 1; v < 7; v++) if (p.ho[c][v] > p.ho[c][b]) b = v;
        cnt[b]++;
      }
      int head = 0;
      for (int v = 1; v < 7; v++) if (cnt[v] > cnt[head]) head = v;
      S[k].push_back(head);
      for (int j = 0; j < 7; j++) {
        if (j == head) continue;
        if (!NonNeg(*DomD(c, head, j), box)) S[k].push_back(j);
      }
    }
    size_t ntup = 1;
    for (int k = 0; k < w.n; k++) ntup *= S[k].size();
    if (verbose) for (int k = 0; k < w.n; k++) { printf("      S%d:", k); for (int v : S[k]) printf(" %d", v); printf("\n"); }
    if (ntup > 128) return false;
    // Inner candidates per contact.
    std::vector<int> I[3];
    for (int k = 0; k < w.n; k++) {
      const int c = w.ch[k];
      std::set<int> s;
      for (const PD &p : pts) {
        int b = 0;
        for (int v = 1; v < 7; v++) if (p.hi[c][v] > p.hi[c][b]) b = v;
        s.insert(b);
      }
      for (size_t q = 0; q < so.blends.size(); q++) s.insert(7 + q);
      // The top three at the center as well.
      std::array<std::pair<double, int>, 7> top;
      for (int v = 0; v < 7; v++) top[v] = {pts[0].hi[c][v], v};
      std::sort(top.rbegin(), top.rend());
      for (int r = 0; r < 3; r++) s.insert(top[r].second);
      I[k].assign(s.begin(), s.end());
    }
    int j[3] = {0, 0, 0};
    std::string tuplog;
    std::map<std::array<int, 3>, std::array<int, 3>> tupres;
    std::function<bool(int)> rec = [&](int k) -> bool {
      if (k == w.n) {
        // Inner choices: argmax set, plus the j's themselves.
        std::vector<int> C[3];
        for (int q = 0; q < w.n; q++) {
          C[q] = I[q];
          if (std::find(C[q].begin(), C[q].end(), j[q]) == C[q].end()) C[q].push_back(j[q]);
        }
        int i[3] = {0, 0, 0};
        const int n1 = C[1].size(), n2 = w.n == 3 ? C[2].size() : 1;
        // Rank the combinations by their worst value over the points.
        std::vector<std::tuple<double, int, int, int>> combos;
        for (int a : C[0]) for (int b = 0; b < n1; b++) for (int c = 0; c < n2; c++) {
          i[0] = a; i[1] = C[1][b]; i[2] = w.n == 3 ? C[2][c] : 0;
          double worst = INFINITY;
          for (const PD &p : pts) {
            double l[3];
            Lams(w, p.u, l);
            double v = 0, den = 0;
            for (int q = 0; q < w.n; q++) {
              v += l[q] * (p.hi[w.ch[q]][i[q]] - p.ho[w.ch[q]][j[q]]);
              den += l[q] * pool.chords[w.ch[q]].len;
            }
            worst = std::min(worst, den > 0 ? v / den : 0.0);
          }
          combos.push_back({worst, i[0], i[1], i[2]});
        }
        std::sort(combos.rbegin(), combos.rend());
        for (size_t r = 0; r < combos.size() && r < g_combos; r++) {
          const int ii[3] = {std::get<1>(combos[r]), std::get<2>(combos[r]), std::get<3>(combos[r])};
          if (verbose) {
            auto D = TupD(wi, ii, j);
            printf("      j %d %d %d  i %d %d %d worst-pt %.3g  bern %.3g\n", j[0], j[1], j[2], ii[0], ii[1], ii[2], std::get<0>(combos[r]), BernsteinLowerD(*D, box));
          }
          if (NonNeg(*TupD(wi, ii, j), box)) {
            tupres[{j[0], j[1], j[2]}] = {ii[0], ii[1], ii[2]};
            if (g_leaflog) {
              char buf[80];
              snprintf(buf, sizeof buf, " %d %d %d %d %d %d ;", j[0], j[1], j[2], ii[0], ii[1], ii[2]);
              tuplog += buf;
            }
            return true;
          }
        }
        return false;
      }
      for (int v : S[k]) { j[k] = v; if (!rec(k + 1)) return false; }
      return true;
    };
    if (!rec(0)) return false;
    {
      // The export line, tuples in Lean's order (`tuples`: index 0 fastest).
      std::string e = "l " + std::to_string(w.n) + " " + std::to_string(w.s);
      for (int k = 0; k < w.n; k++) {
        e += " " + std::to_string(pool.chords[w.ch[k]].a) + " " + std::to_string(pool.chords[w.ch[k]].b) + " " + std::to_string(S[k].size());
        for (int v : S[k]) e += " " + std::to_string(v);
      }
      e += " " + std::to_string(ntup);
      std::array<int, 3> jj{0, 0, 0};
      std::function<void(int)> emit = [&](int k) {
        if (k < 0) {
          const auto &it = tupres.at(jj);
          for (int q = 0; q < w.n; q++) e += " " + std::to_string(it[q]);
          return;
        }
        for (int v : S[k]) { jj[k] = v; emit(k - 1); }
      };
      emit(w.n - 1);
      last_leaf = e;
    }
    if (g_leaflog) {
      std::string l = ch.name;
      char buf[64];
      for (auto &[lo, hi] : box) { snprintf(buf, sizeof buf, " %.17g %.17g", lo, hi); l += buf; }
      l += " | " + std::to_string(w.n);
      for (int k = 0; k < w.n; k++) l += " " + std::to_string(pool.chords[w.ch[k]].a) + " " + std::to_string(pool.chords[w.ch[k]].b);
      l += " " + std::to_string(w.s) + " |";
      for (int k = 0; k < w.n; k++) { for (int v : S[k]) l += " " + std::to_string(v); l += " ,"; }
      l += " |" + tuplog + "\n";
      fputs(l.c_str(), g_leaflog);
    }
    return true;
  }

  void SelfCheck(const double *c) {
    D3 u, w;
    for (int a = 0; a < 3; a++) { u[a] = EvalD(ch.ud[a], c); w[a] = EvalD(ch.wd[a], c); }
    if (DDot(w, w) == 0) return;
    if (ClearDeficit(so.Vd, u, w) < -1e-11) st.selfbad++;
  }
  // Appends the subtree to *out, in preorder (`s axis`, `l ...`, `c`, `f`).
  bool Rec(const Box &box, int depth, std::string *out) {
    if (ch.prune && ch.prune(box)) { st.pruned++; *out += "c\n"; return true; }
    if (st.failed.load() >= max_fail) { st.failed++; *out += "f\n"; return false; }
    // Sample points: center and 2 NV face centers pulled in slightly.
    double c[NV];
    for (int i = 0; i < NV; i++) c[i] = 0.5 * (box[i].first + box[i].second);
    std::vector<PD> pts(2 * NV + 1);
    Point(c, &pts[0]);
    for (int i = 0; i < NV; i++) {
      double x[NV];
      std::copy(c, c + NV, x);
      const double h = 0.48 * (box[i].second - box[i].first);
      x[i] = c[i] - h;
      Point(x, &pts[1 + 2 * i]);
      x[i] = c[i] + h;
      Point(x, &pts[2 + 2 * i]);
    }
    // Rank: at the center over the active pool, then the rest over the top K, normalizing per point.
    thread_local std::vector<std::pair<double, int>> sc;
    sc.clear();
    double best0 = 0;
    for (int wi : active) {
      const double v = Value(pool.wits[wi], pts[0]);
      if (v > -INFINITY) { sc.push_back({v, wi}); best0 = std::max(best0, v); }
    }
    const int K = std::min<int>(g_topk, sc.size());
    std::partial_sort(sc.begin(), sc.begin() + K, sc.end(), [](auto &a, auto &b) { return a.first > b.first; });
    sc.resize(K);
    // Pairs always compete: their values are small on the flex (second order) but they are the robust witnesses there.
    for (int wi : active) if (pool.wits[wi].n == 2) {
      bool in = false;
      for (const auto &x : sc) in = in || x.second == wi;
      if (!in) sc.push_back({0, wi});
    }
    const int K2 = sc.size();
    std::vector<double> score(K2, 1e300);
    for (const PD &p : pts) {
      double best = 1e-300;
      std::vector<double> vs(K2);
      for (int r = 0; r < K2; r++) { vs[r] = Value(pool.wits[sc[r].second], p); if (vs[r] > best) best = vs[r]; }
      for (int r = 0; r < K2; r++) score[r] = std::min(score[r], vs[r] / best);
    }
    std::vector<std::pair<double, int>> order(K2);
    for (int r = 0; r < K2; r++) order[r] = {score[r], sc[r].second};
    std::sort(order.begin(), order.end(), [](auto &a, auto &b) { return a.first > b.first; });
    int done = 0;
    double last = INFINITY;
    // Recently successful witnesses first (neighbouring boxes share them).
    thread_local std::vector<int> mru;
    thread_local const Certifier *mru_owner = nullptr;
    if (mru_owner != this) { mru.clear(); mru_owner = this; }
    for (size_t r = 0; r < mru.size(); r++) {
      const int wi = mru[r];
      if (Value(pool.wits[wi], pts[0]) <= -INFINITY) continue;
      if (Try(wi, box, pts)) {
        st.ok++;
        st.depth_hist[std::min(depth, 63)]++;
        SelfCheck(c);
        mru.erase(mru.begin() + r);
        mru.insert(mru.begin(), wi);
        *out += last_leaf + "\n";
        return true;
      }
    }
    const int try_now = depth >= max_depth - 3 ? 12 * g_try : g_try;
    for (int r = 0; r < K2 && done < try_now; r++) {
      if (order[r].first == -INFINITY) break;
      // Skip near-duplicates (the same contacts with a redundant third chord).
      if (std::abs(order[r].first - last) < 1e-7) continue;
      last = order[r].first;
      done++;
      if (verbose) printf(" rank %d score %.4g %s\n", r, order[r].first, WitName(order[r].second).c_str());
      if (Try(order[r].second, box, pts)) {
        st.ok++;
        st.depth_hist[std::min(depth, 63)]++;
        SelfCheck(c);
        mru.insert(mru.begin(), order[r].second);
        if (mru.size() > 6) mru.pop_back();
        *out += last_leaf + "\n";
        return true;
      }
    }
    if (depth >= max_depth) {
      st.failed++;
      std::lock_guard<std::mutex> l(mu);
      if (fail_boxes.size() < 6) {
        std::string s;
        char buf[80];
        for (auto &[lo, hi] : box) { snprintf(buf, sizeof buf, "[%.6g,%.6g] ", lo, hi); s += buf; }
        fail_boxes.push_back(s);
      }
      if (g_faillog) {
        std::string s = ch.name;
        char buf[64];
        for (auto &[lo, hi] : box) { snprintf(buf, sizeof buf, " %.9g %.9g", lo, hi); s += buf; }
        s += "\n";
        fputs(s.c_str(), g_faillog);
      }
      *out += "f\n";
      return false;
    }
    int best = 0;
    double bw = -1;
    for (int i = 0; i < NV; i++) {
      const double rel = (box[i].second - box[i].first) / (ch.box[i].second - ch.box[i].first);
      if (rel > bw) { bw = rel; best = i; }
    }
    const double m = 0.5 * (box[best].first + box[best].second);
    Box b1 = box, b2 = box;
    b1[best].second = m;
    b2[best].first = m;
    *out += "s " + std::to_string(best) + "\n";
    const bool r1 = Rec(b1, depth + 1, out);
    const bool r2 = Rec(b2, depth + 1, out);
    return r1 && r2;
  }
};

}  // namespace

int main(int argc, char **argv) {
  std::fesetround(FE_TONEAREST);
  Params pr;
  std::string family = "U", only, debug, export_file;
  int max_depth = 26, threads = 24;
  int64_t max_fail = 2000;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--family") family = next();
    else if (a == "--solid") SetSolid(next());
    else if (a == "--frame") g_frame = next();
    else if (a == "--w3") g_w3 = next();
    else if (a == "--m3t") g_m3t = std::stoi(next());
    else if (a == "--polar") g_polar = true;
    else if (a == "--fpolar") g_fpolar = true;
    else if (a == "--e1scale") g_e1scale = Q(std::string_view(next()));
    else if (a == "--e2scale") g_e2scale = Q(std::string_view(next()));
    else if (a == "--model") g_model = next();
    else if (a == "--mu0") pr.mu0 = Q(std::string_view(next()));
    else if (a == "--R") pr.R = std::stod(next());
    else if (a == "--S") pr.S = std::stod(next());
    else if (a == "--Rc") pr.Rc = std::stod(next());
    else if (a == "--Sc") pr.Sc = std::stod(next());
    else if (a == "--nu0") pr.nu0 = Q(std::string_view(next()));
    else if (a == "--R1") pr.R1 = std::stod(next());
    else if (a == "--R2") pr.R2 = std::stod(next());
    else if (a == "--R3") pr.R3 = std::stod(next());
    else if (a == "--Z") pr.Z = std::stod(next());
    else if (a == "--Zc") pr.Zc = std::stod(next());
    else if (a == "--R2c") pr.R2c = std::stod(next());
    else if (a == "--R3c") pr.R3c = std::stod(next());
    else if (a == "--tlo") pr.tlo = Q(std::string_view(next()));
    else if (a == "--thi") pr.thi = Q(std::string_view(next()));
    else if (a == "--zl") pr.zl = Q(std::string_view(next()));
    else if (a == "--zh") pr.zh = Q(std::string_view(next()));
    else if (a == "--tmid") { pr.tmid = true; pr.zmid = std::stod(next()); }
    else if (a == "--regime") pr.regime = std::stoi(next());
    else if (a == "--piece") pr.piece = std::stoi(next());
    else if (a == "--export") export_file = next();
    else if (a == "--sides") {
      pr.sides.clear();
      for (char c : next()) pr.sides.push_back(c - '0');
    }
    else if (a == "--wedge_prune") pr.wedge_prune = true;
    else if (a == "--wp") pr.wp = true;
    else if (a == "--wp_prune") pr.wp_prune = true;
    else if (a == "--only") only = next();
    else if (a == "--debug_box") debug = next();
    else if (a == "--leaflog") g_leaflog = fopen(next().c_str(), "w");
    else if (a == "--faillog") g_faillog = fopen(next().c_str(), "w");
    else if (a == "--double") g_exact = false;
    else if (a == "--exact") g_exact = true;
    else if (a == "--max_depth") max_depth = std::stoi(next());
    else if (a == "--max_fail") max_fail = std::stoll(next());
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--try") g_try = std::stoi(next());
    else if (a == "--topk") g_topk = std::stoi(next());
    else if (a == "--combos") g_combos = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  Solid so;
  LoadSolid(&so);
  Pool pool;
  MakePool(so, &pool);
  std::vector<Chart> charts;
  if (family == "U") AddUCharts(so, pr, &charts);
  else if (family == "W") AddWedgeCharts(so, pr, &charts);
  else if (family == "WP") AddWedgeChartsP(so, pr, &charts);
  else LOG(FATAL) << family;
  for (Chart &c : charts) c.Finish();
  printf("%zu charts, %zu chords, %zu witnesses, %s\n", charts.size(), pool.chords.size(), pool.wits.size(), g_exact ? "exact" : "double");
  struct Task { size_t chart; Box box; int m; std::string out; };
  std::vector<Task> tasks;
  std::vector<std::unique_ptr<Certifier>> certs(charts.size());
  std::vector<std::atomic<int>> pending(charts.size());
  std::vector<std::atomic<bool>> okc(charts.size());
  for (size_t k = 0; k < charts.size(); k++) {
    if (!only.empty()) {
      bool match = false;
      std::stringstream ss(only);
      std::string item;
      while (std::getline(ss, item, ',')) match = match || charts[k].name.find(item) != std::string::npos;
      if (!match) continue;
    }
    certs[k] = std::make_unique<Certifier>(so, pool, charts[k], max_depth, max_fail);
    okc[k] = true;
    const Box &b0 = charts[k].box;
    int cnt = 0;
    for (int m = 0; m < 32; m++) {
      Box b = b0;
      for (int i = 0; i < NV; i++) {
        const double md = 0.5 * (b0[i].first + b0[i].second);
        if (m >> i & 1) b[i].first = md; else b[i].second = md;
      }
      tasks.push_back({k, b, m, ""});
      cnt++;
    }
    pending[k] = cnt;
  }
  if (!debug.empty()) {
    std::stringstream ss(debug);
    std::string name;
    ss >> name;
    Box b;
    for (int i = 0; i < NV; i++) {
      std::string r;
      ss >> r;
      CHECK(std::sscanf(r.c_str(), "%lf,%lf", &b[i].first, &b[i].second) == 2) << r;
    }
    for (size_t k = 0; k < charts.size(); k++)
      if (charts[k].name == name) {
        Certifier c(so, pool, charts[k], max_depth, max_fail);
        printf("active %zu\n", c.active.size());
        c.Debug(b);
        c.verbose = true;
        std::string dummy;
        printf("Rec: %d\n", (int)c.Rec(b, max_depth, &dummy));
      }
    return 0;
  }
  // Interleave charts.
  std::atomic<size_t> nx{0};
  std::mutex om;
  std::atomic<int64_t> tot_ok{0}, tot_fail{0};
  std::vector<std::thread> ts;
  for (int t = 0; t < threads; t++)
    ts.emplace_back([&]() {
      for (;;) {
        const size_t q = nx++;
        if (q >= tasks.size()) return;
        Task &task = tasks[q];
        Certifier &c = *certs[task.chart];
        if (!c.Rec(task.box, 5, &task.out)) okc[task.chart] = false;
        if (--pending[task.chart] == 0) {
          std::lock_guard<std::mutex> l(om);
          std::string hist;
          for (int d = 0; d < 64; d++) if (c.st.depth_hist[d].load()) hist += " " + std::to_string(d) + ":" + std::to_string(c.st.depth_hist[d].load());
          std::array<int, NV> md{};
          size_t maxn = 0;
          for (const auto &[k, d] : c.tup) { for (int i = 0; i < NV; i++) md[i] = std::max(md[i], d->deg[i]); maxn = std::max(maxn, d->exact.t.size()); }
          hist += "  maxdeg";
          for (int i = 0; i < NV; i++) hist += " " + std::to_string(md[i]);
          hist += " maxterms " + std::to_string(maxn);
          if (c.st.selfbad.load()) printf("SELFCHECK %lld leaf centers with positive clearance\n", (long long)c.st.selfbad.load());
          printf("%-14s %s leaves %lld pruned %lld failed %lld tries %lld bern %lld exact %lld polys %zu | %s\n", c.ch.name.c_str(),
                 okc[task.chart] ? "OK  " : "FAIL", (long long)c.st.ok.load(), (long long)c.st.pruned.load(),
                 (long long)c.st.failed.load(), (long long)c.st.tries.load(), (long long)c.st.bern.load(), (long long)c.st.exact_calls.load(), c.tup.size(), hist.c_str());
          for (const auto &f : c.fail_boxes) printf("    fail %s\n", f.c_str());
          fflush(stdout);
          tot_ok += c.st.ok.load();
          tot_fail += c.st.failed.load();
        }
      }
    });
  for (auto &t : ts) t.join();
  if (g_faillog) fclose(g_faillog);
  if (g_leaflog) fclose(g_leaflog);
  if (!export_file.empty()) {
    // Per chart: `chart <id>`, then the tree: the 5 root splits (axes 0..4), then each task's subtree.
    FILE *f = fopen(export_file.c_str(), "w");
    CHECK(f != nullptr) << export_file;
    std::map<size_t, std::array<const std::string *, 32>> by;
    for (const Task &t : tasks) by[t.chart][t.m] = &t.out;
    for (const auto &[k, outs] : by) {
      if (charts[k].id.empty()) continue;
      fprintf(f, "chart %s\n", charts[k].id.c_str());
      std::function<void(int, int)> node = [&](int i, int m) {
        if (i == NV) { fputs(outs[m]->c_str(), f); return; }
        fprintf(f, "s %d\n", i);
        node(i + 1, m);
        node(i + 1, m | 1 << i);
      };
      node(0, 0);
    }
    fclose(f);
  }
  printf("TOTAL leaves %lld failed %lld\n", (long long)tot_ok.load(), (long long)tot_fail.load());
  return 0;
}
