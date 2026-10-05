// capcert (work in progress): cap certificates for the deltoidal
// hexecontahedron's special views (the 2-fold axis view u0 and the two-kite
// view ux; notes/T.md). Near such a view x the identity's first-order cage
// degenerates, so the poses (view u = x + mu a, rotation w) are blown up:
// w = mu (s1 e1 + s2 e2) + mu^2 s3 x, with charts on the faces of the weighted
// cube max(e, |s|/2) = 1 (e = |u - x| / mu) and a cone chart at the identity.
// Each box of a chart is certified by a witness (vertex k, direction c):
// P_j = (N(w) v_k - D(w) v_j) . (u x c) >= 0 for every vertex j, after
// dividing by the largest powers of mu (and of the cone radius t) that divide
// it; then h_{RK}(d) >= h_K(d) for d = u x c, so the pose is not a passage.
// At u0 boxes outside the half-turn cell are pruned.
//
// This version works in double precision (feasibility); the certified version
// will build the polynomials over K = Q(sqrt5, sin 72) (dh_exact.txt), check
// the divisions exactly and bound the boxes in interval arithmetic.
//
// Usage: capcert.exe [--cap u0|ux] [--mu0 0.01] [--max_depth 40] [--threads 60]

#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <map>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"

namespace {

constexpr int NV = 5;  // variables: mu, tau, p1, p2, p3
int g_try = 16;  // witnesses tried per box (best at the center first)
using Exp = std::array<uint8_t, NV>;
using Vec3 = std::array<double, 3>;

double Dot(const Vec3 &a, const Vec3 &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
Vec3 Cross(const Vec3 &a, const Vec3 &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
Vec3 Sub(const Vec3 &a, const Vec3 &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
Vec3 Norm(const Vec3 &a) { const double n = std::sqrt(Dot(a, a)); return {a[0] / n, a[1] / n, a[2] / n}; }

struct Poly {
  std::map<Exp, double> t;
  static Poly Const(double c) { Poly p; if (c != 0) p.t[Exp{}] = c; return p; }
  static Poly Var(int i, double c = 1) { Poly p; Exp e{}; e[i] = 1; p.t[e] = c; return p; }
};
Poly operator+(const Poly &a, const Poly &b) {
  Poly r = a;
  for (const auto &[e, c] : b.t) r.t[e] += c;
  return r;
}
Poly operator-(const Poly &a, const Poly &b) {
  Poly r = a;
  for (const auto &[e, c] : b.t) r.t[e] -= c;
  return r;
}
Poly operator*(const Poly &a, const Poly &b) {
  Poly r;
  for (const auto &[ea, ca] : a.t)
    for (const auto &[eb, cb] : b.t) {
      Exp e;
      for (int i = 0; i < NV; i++) e[i] = ea[i] + eb[i];
      r.t[e] += ca * cb;
    }
  return r;
}
Poly operator*(double s, const Poly &a) {
  Poly r;
  for (const auto &[e, c] : a.t) r.t[e] = s * c;
  return r;
}
using PVec = std::array<Poly, 3>;
PVec PConst(const Vec3 &v) { return {Poly::Const(v[0]), Poly::Const(v[1]), Poly::Const(v[2])}; }
PVec operator+(const PVec &a, const PVec &b) { return {a[0] + b[0], a[1] + b[1], a[2] + b[2]}; }
PVec operator*(const Poly &s, const PVec &a) { return {s * a[0], s * a[1], s * a[2]}; }
PVec operator*(double s, const PVec &a) { return {s * a[0], s * a[1], s * a[2]}; }
Poly PDot(const PVec &a, const PVec &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
Poly PDot(const PVec &a, const Vec3 &c) { return c[0] * a[0] + c[1] * a[1] + c[2] * a[2]; }
PVec PCross(const PVec &a, const PVec &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}

// Drop coefficients below tol; divide by the largest power of variable i.
Poly DivideVar(const Poly &p, int i, double tol = 1e-12) {
  Poly q;
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

double Eval(const Poly &p, const double *x) {
  double s = 0;
  for (const auto &[e, c] : p.t) {
    double v = c;
    for (int i = 0; i < NV; i++) for (int k = 0; k < e[i]; k++) v *= x[i];
    s += v;
  }
  return s;
}

// Dense polynomial for Bernstein: degrees per variable.
struct Dense {
  std::array<int, NV> deg{};
  std::vector<double> c;  // row-major over (d0+1) x ... x (d4+1)
  int Index(const Exp &e) const {
    int idx = 0;
    for (int i = 0; i < NV; i++) idx = idx * (deg[i] + 1) + e[i];
    return idx;
  }
};
Dense ToDense(const Poly &p) {
  Dense d;
  for (const auto &[e, c] : p.t) for (int i = 0; i < NV; i++) d.deg[i] = std::max(d.deg[i], (int)e[i]);
  int n = 1;
  for (int i = 0; i < NV; i++) n *= d.deg[i] + 1;
  d.c.assign(n, 0.0);
  for (const auto &[e, c] : p.t) d.c[d.Index(e)] += c;
  return d;
}

double Binom(int n, int k) {
  double r = 1;
  for (int i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return r;
}

// Lower bound on the box by tensor Bernstein coefficients.
double BernsteinLower(const Dense &d, const std::array<std::pair<double, double>, NV> &box) {
  std::vector<double> c = d.c;
  std::array<int, NV> sz;
  for (int i = 0; i < NV; i++) sz[i] = d.deg[i] + 1;
  std::array<int, NV> stride;
  stride[NV - 1] = 1;
  for (int i = NV - 2; i >= 0; i--) stride[i] = stride[i + 1] * sz[i + 1];
  const int n = c.size();
  for (int ax = 0; ax < NV; ax++) {
    const int D = d.deg[ax];
    if (D == 0 && box[ax].first == 0) continue;
    const double lo = box[ax].first, h = box[ax].second - box[ax].first;
    std::vector<double> col(D + 1), out(D + 1);
    for (int base = 0; base < n; base++) {
      if ((base / stride[ax]) % sz[ax] != 0) continue;
      for (int k = 0; k <= D; k++) col[k] = c[base + k * stride[ax]];
      // substitute x = lo + h y: coefficients in y
      for (int k = 0; k <= D; k++) out[k] = 0;
      for (int j = 0; j <= D; j++) {
        if (col[j] == 0) continue;
        // (lo + h y)^j = sum_k C(j,k) lo^(j-k) h^k y^k
        for (int k = 0; k <= j; k++) out[k] += col[j] * Binom(j, k) * std::pow(lo, j - k) * std::pow(h, k);
      }
      // to Bernstein: b_I = sum_{J<=I} C(I,J)/C(D,J) a_J
      for (int I = 0; I <= D; I++) {
        double s = 0;
        for (int J = 0; J <= I; J++) s += Binom(I, J) / Binom(D, J) * out[J];
        col[I] = s;
      }
      for (int k = 0; k <= D; k++) c[base + k * stride[ax]] = col[k];
    }
  }
  return *std::min_element(c.begin(), c.end());
}

struct Solid {
  std::vector<Vec3> V;
  std::vector<std::pair<int, int>> edges;
};

Solid LoadSolid(const std::string &file) {
  Solid s;
  std::vector<Vec3> slots;
  std::vector<std::vector<int>> faces;
  std::ifstream in(file);
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    if (tag == "vertex") {
      int i;
      Vec3 p;
      ss >> i >> p[0] >> p[1] >> p[2];
      slots.push_back(p);
    } else if (tag == "face") {
      std::vector<int> f;
      int k;
      while (ss >> k) f.push_back(k);
      faces.push_back(f);
    }
  }
  std::vector<int> sv;
  for (const Vec3 &p : slots) {
    int found = -1;
    for (size_t j = 0; j < s.V.size(); j++)
      if (std::abs(p[0] - s.V[j][0]) + std::abs(p[1] - s.V[j][1]) + std::abs(p[2] - s.V[j][2]) < 1e-12) found = j;
    if (found < 0) { found = s.V.size(); s.V.push_back(p); }
    sv.push_back(found);
  }
  for (const auto &face : faces) {
    std::vector<int> f;
    for (int x : face) if (std::find(f.begin(), f.end(), sv[x]) == f.end()) f.push_back(sv[x]);
    Vec3 c{0, 0, 0};
    for (int v : f) for (int a = 0; a < 3; a++) c[a] += s.V[v][a] / f.size();
    const Vec3 n = Norm(c), e1 = Norm(Sub(s.V[f[0]], c)), e2 = Cross(n, e1);
    std::sort(f.begin(), f.end(), [&](int a, int b) {
      return std::atan2(Dot(Sub(s.V[a], c), e2), Dot(Sub(s.V[a], c), e1)) <
             std::atan2(Dot(Sub(s.V[b], c), e2), Dot(Sub(s.V[b], c), e1));
    });
    for (size_t k = 0; k < f.size(); k++) {
      const auto e = std::minmax(f[k], f[(k + 1) % f.size()]);
      if (std::find(s.edges.begin(), s.edges.end(), std::pair<int, int>(e.first, e.second)) == s.edges.end())
        s.edges.push_back({e.first, e.second});
    }
  }
  return s;
}

// Vertices whose projection along u is on the shadow boundary (within tol).
std::vector<int> SupportVertices(const Solid &s, const Vec3 &u) {
  const Vec3 a = Norm(Cross(u, {0, 0, 1})), b = Cross(u, a);
  const int n = s.V.size();
  std::vector<std::array<double, 2>> P(n);
  for (int i = 0; i < n; i++) P[i] = {Dot(s.V[i], a), Dot(s.V[i], b)};
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

struct Witness {
  int k;
  Vec3 c;
};

struct Chart {
  std::string kind;  // "Fe", "cone", "face"
  int side = 0, axis = 0;
  double sign = 1;
  std::array<std::pair<double, double>, NV> box;
  PVec u, w;
  Poly cell;  // half-turn cell (prune if > 0), empty if unused
  bool cone = false;
  std::array<double, 2> sM_A{}, sM_B{};  // s_M(tau) = A + tau B (Fe charts: for the M-cone exclusion)
};

struct Problem {
  Solid s;
  Vec3 x, e1, e2;
  std::vector<Witness> W;
  bool half_turn = false;
  bool tie_cones = false;  // cone charts at the tie M(u) (ux)
  bool aniso = false;      // anisotropic weights (ux): w = mu s1 (x cross a) + mu^2 (s2 a + s3 x)
  double mu0 = 0.01, t0 = 0.25;
};

Chart MakeChart(const Problem &pr, const std::string &kind, int side, int axis, double sign) {
  Chart ch;
  ch.kind = kind;
  ch.side = side;
  ch.axis = axis;
  ch.sign = sign;
  const Poly mu = Poly::Var(0), tau = Poly::Var(1);
  const Poly p[3] = {Poly::Var(2), Poly::Var(3), Poly::Var(4)};
  Vec3 A, B;
  if (side == 0) { A = pr.e1; B = pr.e2; }
  else if (side == 1) { A = {-pr.e1[0], -pr.e1[1], -pr.e1[2]}; B = pr.e2; }
  else if (side == 2) { A = pr.e2; B = pr.e1; }
  else { A = {-pr.e2[0], -pr.e2[1], -pr.e2[2]}; B = pr.e1; }
  const PVec a = PConst(A) + tau * PConst(B);
  Poly e = Poly::Const(1), s[3];
  if (kind == "Fe") {
    for (int i = 0; i < 3; i++) s[i] = p[i];
    const Vec3 XA = Cross(pr.x, A), XB = Cross(pr.x, B);
    ch.sM_A = pr.aniso ? std::array<double, 2>{1, 0} : std::array<double, 2>{Dot(XA, pr.e1), Dot(XA, pr.e2)};
    ch.sM_B = pr.aniso ? std::array<double, 2>{0, 0} : std::array<double, 2>{Dot(XB, pr.e1), Dot(XB, pr.e2)};
    ch.box = {{{0, pr.mu0}, {-1, 1}, {-2, 2}, {-2, 2}, {-2, 2}}};
  } else if (kind == "Mcone") {
    // s = s_M(tau) + t sigma, s_M = x cross a (the tie M(u) = H_u H_x in the
    // weighted chart), sigma on the cube face (axis, sign).
    ch.cone = true;
    const Vec3 XA = Cross(pr.x, A), XB = Cross(pr.x, B);
    // In the anisotropic chart w_M = mu (x cross a) is exactly s = (1, 0, 0).
    const Poly sM[3] = {pr.aniso ? Poly::Const(1) : Poly::Const(Dot(XA, pr.e1)) + Dot(XB, pr.e1) * tau,
                        pr.aniso ? Poly() : Poly::Const(Dot(XA, pr.e2)) + Dot(XB, pr.e2) * tau, Poly()};
    int o = 0;
    for (int i = 0; i < 3; i++) {
      const Poly sig = i == axis ? Poly::Const(sign) : p[1 + o++];
      s[i] = sM[i] + p[0] * sig;
    }
    ch.box = {{{0, pr.mu0}, {-1, 1}, {0, pr.t0}, {-1, 1}, {-1, 1}}};
    ch.sM_A = pr.aniso ? std::array<double, 2>{1, 0} : std::array<double, 2>{Dot(XA, pr.e1), Dot(XA, pr.e2)};
    ch.sM_B = pr.aniso ? std::array<double, 2>{0, 0} : std::array<double, 2>{Dot(XB, pr.e1), Dot(XB, pr.e2)};
  } else if (kind == "cone") {
    ch.cone = true;
    int o = 0;
    for (int i = 0; i < 3; i++) {
      if (i == axis) s[i] = Poly::Const(sign) * p[0];
      else s[i] = p[1 + o++] * p[0];
    }
    ch.box = {{{0, pr.mu0}, {-1, 1}, {0, pr.t0}, {-1, 1}, {-1, 1}}};
  } else {
    e = p[0];
    int o = 0;
    for (int i = 0; i < 3; i++) s[i] = i == axis ? Poly::Const(2 * sign) : p[1 + o++];
    ch.box = {{{0, pr.mu0}, {-1, 1}, {0, 1}, {-2, 2}, {-2, 2}}};
  }
  ch.u = PConst(pr.x) + (mu * e) * a;
  if (pr.aniso) {
    // Weights: the tie direction m(a) = x cross a weight 1; a and x weight 2.
    const PVec m = PCross(PConst(pr.x), a);
    ch.w = (mu * s[0]) * m + ((mu * mu) * s[1]) * a + ((mu * mu) * s[2]) * PConst(pr.x);
  } else {
    ch.w = (mu * s[0]) * PConst(pr.e1) + (mu * s[1]) * PConst(pr.e2) + ((mu * mu) * s[2]) * PConst(pr.x);
  }
  if (pr.half_turn) {
    // 2 u^T N G u - |u|^2 (tr(N G) + tr N), G = H_x.
    const Poly ww = PDot(ch.w, ch.w), one_m = Poly::Const(1) - ww;
    auto Nvec = [&](const Vec3 &v) {
      return one_m * PConst(v) + (2.0 * PDot(ch.w, v)) * ch.w + 2.0 * PCross(ch.w, PConst(v));
    };
    std::array<PVec, 3> NGcol, Ncol;
    for (int j = 0; j < 3; j++) {
      Vec3 g, ej{0, 0, 0};
      ej[j] = 1;
      for (int i = 0; i < 3; i++) g[i] = 2 * pr.x[i] * pr.x[j] - (i == j ? 1 : 0);
      NGcol[j] = Nvec(g);
      Ncol[j] = Nvec(ej);
    }
    PVec NGu;
    for (int i = 0; i < 3; i++) NGu[i] = NGcol[0][i] * ch.u[0] + NGcol[1][i] * ch.u[1] + NGcol[2][i] * ch.u[2];
    const Poly uNGu = PDot(ch.u, NGu);
    const Poly trNG = NGcol[0][0] + NGcol[1][1] + NGcol[2][2], trN = Ncol[0][0] + Ncol[1][1] + Ncol[2][2];
    Poly cell = 2.0 * uNGu - PDot(ch.u, ch.u) * (trNG + trN);
    cell = DivideVar(cell, 0);
    if (ch.cone) cell = DivideVar(cell, 2);
    ch.cell = cell;
  }
  return ch;
}

struct WitnessPolys {
  std::vector<Dense> P;  // per vertex j
};

WitnessPolys MakeWitness(const Problem &pr, const Chart &ch, const Witness &wt) {
  const Poly ww = PDot(ch.w, ch.w), D = Poly::Const(1) + ww;
  const Vec3 &vk = pr.s.V[wt.k];
  const PVec Nvk = (Poly::Const(1) - ww) * PConst(vk) + (2.0 * PDot(ch.w, vk)) * ch.w + 2.0 * PCross(ch.w, PConst(vk));
  const PVec d = PCross(ch.u, PConst(wt.c));
  const Poly base = PDot(Nvk, d);
  const PVec Dd = {D * d[0], D * d[1], D * d[2]};
  WitnessPolys out;
  for (const Vec3 &vj : pr.s.V) {
    Poly p = base - PDot(Dd, vj);
    p = DivideVar(p, 0);
    if (ch.cone) p = DivideVar(p, 2);
    out.P.push_back(ToDense(p));
  }
  return out;
}

struct Stats {
  std::atomic<int64_t> ok{0}, pruned{0}, failed{0};
};

struct Certifier {
  const Problem &pr;
  const Chart &ch;
  int max_depth;
  Stats *stats;
  std::vector<std::unique_ptr<WitnessPolys>> cache;
  std::mutex mu;
  Dense cell;
  std::vector<std::string> fail_boxes;

  Certifier(const Problem &p, const Chart &c, int md, Stats *st) : pr(p), ch(c), max_depth(md), stats(st) {
    cache.resize(pr.W.size());
    if (!ch.cell.t.empty()) cell = ToDense(ch.cell);
  }
  const WitnessPolys &Get(int wi) {
    std::lock_guard<std::mutex> l(mu);
    if (!cache[wi]) cache[wi] = std::make_unique<WitnessPolys>(MakeWitness(pr, ch, pr.W[wi]));
    return *cache[wi];
  }

  bool InCone(const std::array<std::pair<double, double>, NV> &box) const {
    if (ch.kind != "Fe") return false;
    bool in_i = true;
    for (int i = 2; i < 5; i++)
      if (std::max(std::abs(box[i].first), std::abs(box[i].second)) > pr.t0) in_i = false;
    if (in_i) return true;
    if (!pr.tie_cones) return false;
    // Inside the M-cone region for every tau of the box: |s - s_M(tau)|_inf <= t0.
    if (std::max(std::abs(box[4].first), std::abs(box[4].second)) > pr.t0) return false;
    for (int c = 0; c < 2; c++) {
      for (double tau : {box[1].first, box[1].second}) {
        const double m = ch.sM_A[c] + tau * ch.sM_B[c];
        if (std::max(std::abs(box[2 + c].first - m), std::abs(box[2 + c].second - m)) > pr.t0) return false;
      }
    }
    return true;
  }

  bool Rec(std::array<std::pair<double, double>, NV> box, int depth) {
    if (InCone(box)) return true;
    if (!cell.c.empty() && BernsteinLower(cell, box) > 1e-12) { stats->pruned++; return true; }
    // Screen witnesses at the center.
    double x[NV];
    for (int i = 0; i < NV; i++) x[i] = 0.5 * (box[i].first + box[i].second);
    Vec3 u, w;
    for (int a = 0; a < 3; a++) { u[a] = Eval(ch.u[a], x); w[a] = Eval(ch.w[a], x); }
    const double ww = Dot(w, w), Dw = 1 + ww;
    std::vector<std::pair<double, int>> sc;
    for (size_t wi = 0; wi < pr.W.size(); wi++) {
      const Vec3 &v = pr.s.V[pr.W[wi].k];
      const Vec3 wv = Cross(w, v);
      Vec3 rv;
      for (int a = 0; a < 3; a++) rv[a] = ((1 - ww) * v[a] + 2 * w[a] * Dot(w, v) + 2 * wv[a]) / Dw;
      const Vec3 d = Cross(u, pr.W[wi].c);
      double mx = -1e300;
      for (const Vec3 &vj : pr.s.V) mx = std::max(mx, Dot(vj, d));
      sc.push_back({(Dot(rv, d) - mx) / std::sqrt(Dot(d, d)), (int)wi});
    }
    const int ntry = std::min<int>(g_try, sc.size());
    std::partial_sort(sc.begin(), sc.begin() + ntry, sc.end(),
                      [](auto &a, auto &b) { return a.first > b.first; });
    for (int r = 0; r < ntry; r++) {
      if (sc[r].first <= -1e-15) break;
      const WitnessPolys &wp = Get(sc[r].second);
      bool all = true;
      for (const Dense &P : wp.P) {
        // Non-strict: P >= 0 suffices (a tie is not a passage); the double-precision
        // prototype allows rounding noise, the exact version checks >= 0 exactly.
        if (!(BernsteinLower(P, box) >= -1e-13)) { all = false; break; }
      }
      if (all) { stats->ok++; return true; }
    }
    if (depth >= max_depth) {
      stats->failed++;
      std::lock_guard<std::mutex> l(mu);
      if (fail_boxes.size() < 5) {
        std::string s;
        for (auto &[lo, hi] : box) s += std::to_string(lo) + ".." + std::to_string(hi) + " ";
        fail_boxes.push_back(s);
      }
      return false;
    }
    // Split the widest dimension relative to the chart box.
    int best = 0;
    double bw = -1;
    for (int i = 0; i < NV; i++) {
      const double rel = (box[i].second - box[i].first) / (ch.box[i].second - ch.box[i].first);
      if (rel > bw) { bw = rel; best = i; }
    }
    const double m = 0.5 * (box[best].first + box[best].second);
    auto b1 = box, b2 = box;
    b1[best].second = m;
    b2[best].first = m;
    const bool r1 = Rec(b1, depth + 1);
    const bool r2 = Rec(b2, depth + 1);
    return r1 && r2;
  }
};

}  // namespace

int main(int argc, char **argv) {
  std::string cap = "u0";
  double mu0 = 0.01;
  int max_depth = 40, threads = 60;
  std::string only;
  bool aniso = false;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--cap") cap = next();
    else if (a == "--mu0") mu0 = std::stod(next());
    else if (a == "--max_depth") max_depth = std::stoi(next());
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--try") g_try = std::stoi(next());
    else if (a == "--aniso") aniso = true;
    else if (a == "--only") only = next();  // kind:side:axis:sign, e.g. Fe:2:0:1 (prefixes allowed)
    else LOG(FATAL) << "unknown argument " << a;
  }
  Problem pr;
  pr.s = LoadSolid("dh_model.txt");
  pr.mu0 = mu0;
  if (cap == "u0") {
    pr.x = Norm({0.30901699437494740, 0.42532540417601999, 0.85065080835203999});
    pr.half_turn = true;
  } else {
    pr.x = Norm({std::cos(M_PI / 10), std::sin(M_PI / 10), 2});
    pr.tie_cones = true;
  }
  pr.aniso = aniso;
  pr.e1 = Norm(Cross(pr.x, {0, 0, 1}));
  pr.e2 = Cross(pr.x, pr.e1);
  const std::vector<int> supp = SupportVertices(pr.s, pr.x);
  std::vector<std::vector<int>> nb(pr.s.V.size());
  for (auto &[a, b] : pr.s.edges) { nb[a].push_back(b); nb[b].push_back(a); }
  for (int k : supp) {
    std::vector<int> others = nb[k];
    for (int m : supp) if (m != k && std::find(others.begin(), others.end(), m) == others.end()) others.push_back(m);
    for (int m : others) {
      pr.W.push_back({k, Sub(pr.s.V[m], pr.s.V[k])});
      pr.W.push_back({k, Sub(pr.s.V[k], pr.s.V[m])});
    }
  }
  printf("cap %s: %zu vertices, %zu edges, %zu support vertices, %zu witnesses\n", cap.c_str(), pr.s.V.size(),
         pr.s.edges.size(), supp.size(), pr.W.size());
  std::vector<Chart> charts;
  for (int side = 0; side < 4; side++) {
    charts.push_back(MakeChart(pr, "Fe", side, 0, 1));
    for (int ax = 0; ax < 3; ax++)
      for (double sg : {1.0, -1.0}) {
        charts.push_back(MakeChart(pr, "cone", side, ax, sg));
        if (pr.tie_cones) charts.push_back(MakeChart(pr, "Mcone", side, ax, sg));
        charts.push_back(MakeChart(pr, "face", side, ax, sg));
      }
  }
  // Tasks: (chart, sub-box): each chart's box split 4 x 4 over (mu, tau).
  struct Task { size_t chart; std::array<std::pair<double, double>, NV> box; };
  std::vector<Task> tasks;
  std::vector<std::unique_ptr<Certifier>> certs(charts.size());
  std::vector<std::unique_ptr<Stats>> stats(charts.size());
  std::vector<std::atomic<int>> pending(charts.size());
  std::vector<std::atomic<bool>> chart_ok(charts.size());
  for (size_t k = 0; k < charts.size(); k++) {
    const Chart &ch = charts[k];
    if (!only.empty()) {
      const std::string id = ch.kind + ":" + std::to_string(ch.side) + ":" + std::to_string(ch.axis) + ":" +
                             (ch.sign > 0 ? "1" : "-1");
      bool match = false;
      std::stringstream ss(only);
      std::string item;
      while (std::getline(ss, item, ',')) match = match || id.rfind(item, 0) == 0;
      if (!match) continue;
    }
    stats[k] = std::make_unique<Stats>();
    certs[k] = std::make_unique<Certifier>(pr, ch, max_depth, stats[k].get());
    chart_ok[k] = true;
    pending[k] = 16;
    for (int i = 0; i < 4; i++)
      for (int j = 0; j < 4; j++) {
        auto b = ch.box;
        const double m0 = b[0].first, m1 = b[0].second, t0 = b[1].first, t1 = b[1].second;
        b[0] = {m0 + (m1 - m0) * i / 4, m0 + (m1 - m0) * (i + 1) / 4};
        b[1] = {t0 + (t1 - t0) * j / 4, t0 + (t1 - t0) * (j + 1) / 4};
        tasks.push_back({k, b});
      }
  }
  std::atomic<size_t> next{0};
  std::mutex out_mu;
  std::vector<std::thread> ts;
  for (int t = 0; t < threads; t++) {
    ts.emplace_back([&]() {
      for (;;) {
        const size_t q = next++;
        if (q >= tasks.size()) return;
        const Task &task = tasks[q];
        // Sub-boxes start at depth 4 (two splits each of mu and tau).
        const bool ok = certs[task.chart]->Rec(task.box, 4);
        if (!ok) chart_ok[task.chart] = false;
        if (--pending[task.chart] == 0) {
          const Chart &ch = charts[task.chart];
          const Stats &st = *stats[task.chart];
          std::lock_guard<std::mutex> l(out_mu);
          printf("%-5s side %d axis %d sign %+.0f: %s  boxes %lld pruned %lld failed %lld\n", ch.kind.c_str(),
                 ch.side, ch.axis, ch.sign, chart_ok[task.chart] ? "OK" : "FAIL", (long long)st.ok.load(),
                 (long long)st.pruned.load(), (long long)st.failed.load());
          for (const auto &s : certs[task.chart]->fail_boxes) printf("    fail %s\n", s.c_str());
          fflush(stdout);
        }
      }
    });
  }
  for (auto &t : ts) t.join();
  return 0;
}
