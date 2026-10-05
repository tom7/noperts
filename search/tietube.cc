// tietube: tie tubes for the deltoidal hexecontahedron (see dh_tie_data.py
// and notes/T.md). For a pinning normal x (the plane x^perp holds an
// antipodal pair of 5-fold and of 2-fold vertices), L = sigma_x K, and a view
// u, the pose R = H_u S H_x is a passage iff S L's shadow along u lies
// strictly inside K's (both shadows are centrally symmetric). Near S = I the
// shadows of L and K touch at exact contacts (L-vertices equal to K-vertices
// or inside K-edges), so no rational model can certify these poses; this
// program uses the exact solid (coordinates in K = Q(sqrt5, sin 72)).
//
// Certificate for a view triangle (corners P_c; u = sum lambda_c P_c) and a
// radius rho: every S with Cayley vector w, |w|_inf <= rho, is ruled out. On
// each cube face, w = t sigma, sigma = (s1, s2, +-1) (permuted), t in
// [0, rho]; the face is covered by boxes in (s1, s2), each with a witness:
// an L-vertex q and a direction c (an edge of K through q's touching point),
// d = u x c, such that for every vertex j of K
//   P_j = (N(w) q - D(w) v_j) . d >= 0          (Cayley: S = N/D)
// on the box (for the "tied" j, with q - v_j parallel to c exactly, the w^0
// term vanishes identically and P_j / t is bounded instead). Then
// h_{S L}(d) >= (S q).d >= max_j v_j.d = h_K(d): not strictly inside. P_j is
// linear in lambda, so its corners suffice; each corner polynomial has degree
// <= 2 in s1, s2, t and is bounded below by tensor Bernstein coefficients in
// outward-rounded interval arithmetic from exact K coefficients.
//
// Output: per (normal, code triangle) a quadtree of view nodes with their
// certified rho (the largest of a ladder 1/8, 1/16, ... that works; a node
// is split when it fails down to --min_rho).
//
// Usage: tietube.exe [--data dh_tie_data.txt] [--normals 0,1,..] [--t t1,t2,..]
//          [--trees_dir trees_r1] [--bdd codebdd.json] [--out_dir tie]
//          [--max_depth 8] [--min_rho 1/1024] [--threads 60]

#include <algorithm>
#include <atomic>
#include <cfenv>
#include <filesystem>
#include <functional>
#include <cmath>
#include <cstdio>
#include <format>
#include <fstream>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"
#include "exact5d.h"
#include "geom5d.h"
#include "tubeatlas5d.h"

namespace {

using Q = BigRat;

// ----- The field K = Q(sqrt5, s), s^2 = (5 + sqrt5)/8 -----
struct KNum {
  Q a{0}, b{0}, c{0}, d{0};  // a + b sqrt5 + c s + d s sqrt5
};
KNum operator+(const KNum &x, const KNum &y) { return {x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d}; }
KNum operator-(const KNum &x, const KNum &y) { return {x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d}; }
KNum operator*(const KNum &x, const KNum &y) {
  const Q p = x.c * y.c + Q(5) * x.d * y.d, q = x.c * y.d + x.d * y.c;
  return {x.a * y.a + Q(5) * x.b * y.b + (Q(5) * p + Q(5) * q) / Q(8),
          x.a * y.b + x.b * y.a + (p + Q(5) * q) / Q(8),
          x.a * y.c + Q(5) * x.b * y.d + x.c * y.a + Q(5) * x.d * y.b,
          x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a};
}
KNum Scale(const KNum &x, const Q &r) { return {x.a * r, x.b * r, x.c * r, x.d * r}; }
bool IsZero(const KNum &x) {
  return x.a == Q(0) && x.b == Q(0) && x.c == Q(0) && x.d == Q(0);
}
using KVec = std::array<KNum, 3>;
KNum Dot(const KVec &x, const KVec &y) { return x[0] * y[0] + x[1] * y[1] + x[2] * y[2]; }
KVec Cross(const KVec &x, const KVec &y) {
  return {x[1] * y[2] - x[2] * y[1], x[2] * y[0] - x[0] * y[2], x[0] * y[1] - x[1] * y[0]};
}
KVec Sub(const KVec &x, const KVec &y) { return {x[0] - y[0], x[1] - y[1], x[2] - y[2]}; }
KVec FromQ(const exact5d::VecQ &p) {
  return {KNum{p[0], Q(0), Q(0), Q(0)}, KNum{p[1], Q(0), Q(0), Q(0)}, KNum{p[2], Q(0), Q(0), Q(0)}};
}

// ----- Outward-rounded double intervals -----
struct Iv {
  double lo = 0, hi = 0;
};
double Dn(double x) { return std::nextafter(x, -INFINITY); }
double Up(double x) { return std::nextafter(x, INFINITY); }
Iv IvOf(double x) { return {x, x}; }
Iv operator+(Iv x, Iv y) { return {Dn(x.lo + y.lo), Up(x.hi + y.hi)}; }
Iv operator-(Iv x, Iv y) { return {Dn(x.lo - y.hi), Up(x.hi - y.lo)}; }
Iv operator*(Iv x, Iv y) {
  const double p[4] = {x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi};
  return {Dn(*std::min_element(p, p + 4)), Up(*std::max_element(p, p + 4))};
}
Iv operator*(double s, Iv y) { return IvOf(s) * y; }
Iv Hull(Iv x, Iv y) { return {std::min(x.lo, y.lo), std::max(x.hi, y.hi)}; }

// A rational as an interval (exact enclosure of its double rounding).
Iv IvOfQ(const Q &q) {
  const double d = q.ToDouble();
  return {Dn(Dn(d)), Up(Up(d))};
}
// sqrt5 and s: rigorous enclosures (checked by squaring in rationals).
Iv kSqrt5, kS;
void InitConstants() {
  const Q r5lo("2236067977499789/1000000000000000"), r5hi("2236067977499790/1000000000000000");
  CHECK(r5lo * r5lo < Q(5) && Q(5) < r5hi * r5hi);
  kSqrt5 = {Dn(r5lo.ToDouble()), Up(r5hi.ToDouble())};
  // s^2 = (5 + sqrt5)/8 in [(5 + r5lo)/8, (5 + r5hi)/8].
  const Q slo("951056516295153/1000000000000000"), shi("951056516295154/1000000000000000");
  CHECK(slo * slo < (Q(5) + r5lo) / Q(8) && (Q(5) + r5hi) / Q(8) < shi * shi);
  kS = {Dn(slo.ToDouble()), Up(shi.ToDouble())};
}
Iv IvOfK(const KNum &x) {
  return IvOfQ(x.a) + IvOfQ(x.b) * kSqrt5 + IvOfQ(x.c) * kS + IvOfQ(x.d) * (kSqrt5 * kS);
}

KNum ParseK(std::istringstream &ss) {
  std::string t[4];
  for (auto &s : t) CHECK(ss >> s);
  return {Q(std::string_view(t[0])), Q(std::string_view(t[1])), Q(std::string_view(t[2])),
          Q(std::string_view(t[3]))};
}
KVec ParseKVec(std::istringstream &ss) { return {ParseK(ss), ParseK(ss), ParseK(ss)}; }

struct Witness {
  int i;               // L-vertex
  KVec c;              // direction
  std::vector<int> tied;
};
struct Normal {
  KVec x;
  std::vector<KVec> L;
  std::vector<Witness> w;
};
struct Data {
  std::vector<KVec> V;
  std::vector<Normal> normals;
};

Data LoadData(const std::string &file) {
  Data d;
  std::ifstream in(file);
  CHECK(in.good()) << file;
  std::string line;
  while (std::getline(in, line)) {
    std::istringstream ss(line);
    std::string tag;
    ss >> tag;
    if (tag == "V") {
      int j;
      ss >> j;
      CHECK(j == (int)d.V.size());
      d.V.push_back(ParseKVec(ss));
    } else if (tag == "X") {
      int n;
      ss >> n;
      CHECK(n == (int)d.normals.size());
      d.normals.push_back({ParseKVec(ss), {}, {}});
    } else if (tag == "L") {
      int n, i;
      ss >> n >> i;
      CHECK(i == (int)d.normals[n].L.size());
      d.normals[n].L.push_back(ParseKVec(ss));
    } else if (tag == "W") {
      int n, i;
      ss >> n >> i;
      Witness w{i, ParseKVec(ss), {}};
      std::string tied;
      ss >> tied;
      CHECK(tied == "tied");
      int j;
      while (ss >> j) w.tied.push_back(j);
      d.normals[n].w.push_back(w);
    }
  }
  // Re-verify the exact facts the certificate relies on: L = sigma_x K and
  // q - v_j parallel to c for the tied j (and for no other j).
  for (const Normal &nm : d.normals) {
    const KNum xx = Dot(nm.x, nm.x);
    for (size_t i = 0; i < d.V.size(); i++) {
      // L_i (x.x) = v_i (x.x) - 2 (v_i.x) x.
      const KNum vx = Dot(d.V[i], nm.x);
      for (int k = 0; k < 3; k++) {
        CHECK(IsZero(nm.L[i][k] * xx - (d.V[i][k] * xx - Scale(vx * nm.x[k], Q(2))))) << "L is not sigma_x K";
      }
    }
    for (const Witness &w : nm.w) {
      for (size_t j = 0; j < d.V.size(); j++) {
        const KVec cr = Cross(Sub(nm.L[w.i], d.V[j]), w.c);
        const bool par = IsZero(cr[0]) && IsZero(cr[1]) && IsZero(cr[2]);
        const bool listed = std::find(w.tied.begin(), w.tied.end(), (int)j) != w.tied.end();
        CHECK(par == listed) << "tied set mismatch";
      }
    }
  }
  return d;
}

// Interval polynomial in (s1, s2, t), degree <= 2 in each: c[e1][e2][et].
struct Poly {
  Iv c[3][3][3];
  Poly() { for (auto &a : c) for (auto &b : a) for (auto &x : b) x = IvOf(0); }
};

// Lower bound of p on [s1lo, s1hi] x [s2lo, s2hi] x [0, rho] (tensor
// Bernstein, interval arithmetic).
double BernsteinLower(const Poly &p, double s1lo, double s1hi, double s2lo, double s2hi, double rho) {
  // Substitute s1 = s1lo + h1 y1, s2 = s2lo + h2 y2, t = rho y3.
  const double lo[3] = {s1lo, s2lo, 0}, h[3] = {s1hi - s1lo, s2hi - s2lo, rho};
  Iv c[3][3][3];
  for (auto &a : c) for (auto &b : a) for (auto &x : b) x = IvOf(0);
  auto expand = [&](int e, int axis, Iv out[3]) {
    const Iv L = IvOf(lo[axis]), H = IvOf(h[axis]);
    out[0] = IvOf(e == 0 ? 1 : 0); out[1] = IvOf(0); out[2] = IvOf(0);
    if (e == 1) { out[0] = L; out[1] = H; }
    if (e == 2) { out[0] = L * L; out[1] = 2.0 * (L * H); out[2] = H * H; }
  };
  for (int e1 = 0; e1 < 3; e1++)
    for (int e2 = 0; e2 < 3; e2++)
      for (int e3 = 0; e3 < 3; e3++) {
        const Iv v = p.c[e1][e2][e3];
        if (v.lo == 0 && v.hi == 0) continue;
        Iv x1[3], x2[3], x3[3];
        expand(e1, 0, x1); expand(e2, 1, x2); expand(e3, 2, x3);
        for (int a = 0; a <= e1; a++)
          for (int b = 0; b <= e2; b++)
            for (int g = 0; g <= e3; g++) c[a][b][g] = c[a][b][g] + v * (x1[a] * (x2[b] * x3[g]));
      }
  // Degree-2 Bernstein along each axis: b0 = c0, b1 = c0 + c1/2, b2 = c0 + c1 + c2.
  auto tob = [](Iv &x0, Iv &x1, Iv &x2) {
    const Iv b0 = x0, b1 = x0 + 0.5 * x1, b2 = x0 + x1 + x2;
    x0 = b0; x1 = b1; x2 = b2;
  };
  for (int b = 0; b < 3; b++) for (int g = 0; g < 3; g++) tob(c[0][b][g], c[1][b][g], c[2][b][g]);
  for (int a = 0; a < 3; a++) for (int g = 0; g < 3; g++) tob(c[a][0][g], c[a][1][g], c[a][2][g]);
  for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) tob(c[a][b][0], c[a][b][1], c[a][b][2]);
  double m = INFINITY;
  for (auto &a : c) for (auto &b : a) for (auto &x : b) m = std::min(m, x.lo);
  return m;
}

// Per (witness, corner) interval data: the polynomials depend on sigma
// through sigma.g, (sigma.q)(sigma.D) and |sigma|^2.
struct CornerData {
  Iv g[3], q[3], D[3];
  Iv qD;
  std::vector<Iv> vD;  // v_j . D
};

// sigma on face (axis f, sign sg): sigma_k = s1 if k == a1, s2 if k == a2, sg if k == f.
struct Face {
  int f, a1, a2;
  double sg;
};

// Linear form sigma.v as (coef of s1, coef of s2, const).
void LinForm(const Face &F, const Iv v[3], Iv out[3]) {
  out[0] = v[F.a1];
  out[1] = v[F.a2];
  out[2] = F.sg * v[F.f];
}

// Add scale * (sigma.p)(sigma.r) t^tp to poly.
void AddBilinear(Poly *P, const Face &F, const Iv p[3], const Iv r[3], int tp, Iv scale) {
  Iv lp[3], lr[3];
  LinForm(F, p, lp);
  LinForm(F, r, lr);
  const int mon[3][2] = {{1, 0}, {0, 1}, {0, 0}};
  for (int x = 0; x < 3; x++)
    for (int y = 0; y < 3; y++) {
      Iv &cell = P->c[mon[x][0] + mon[y][0]][mon[x][1] + mon[y][1]][tp];
      cell = cell + scale * (lp[x] * lr[y]);
    }
}
void AddLinear(Poly *P, const Face &F, const Iv g[3], int tp, Iv scale) {
  Iv l[3];
  LinForm(F, g, l);
  P->c[1][0][tp] = P->c[1][0][tp] + scale * l[0];
  P->c[0][1][tp] = P->c[0][1][tp] + scale * l[1];
  P->c[0][0][tp] = P->c[0][0][tp] + scale * l[2];
}
void AddNormSq(Poly *P, int tp, Iv scale) {  // |sigma|^2 = s1^2 + s2^2 + 1
  P->c[2][0][tp] = P->c[2][0][tp] + scale;
  P->c[0][2][tp] = P->c[0][2][tp] + scale;
  P->c[0][0][tp] = P->c[0][0][tp] + scale;
}

// The tied polynomial / t: 2 sigma.g + 2 t [(sigma.q)(sigma.D) - |sigma|^2 qD].
Poly TiedPoly(const Face &F, const CornerData &cd) {
  Poly P;
  AddLinear(&P, F, cd.g, 0, IvOf(2));
  AddBilinear(&P, F, cd.q, cd.D, 1, IvOf(2));
  AddNormSq(&P, 1, IvOf(-2) * cd.qD);
  return P;
}
// Non-tied j: (qD - vjD) + 2t sigma.g + t^2 [2(sigma.q)(sigma.D) - |sigma|^2 (qD + vjD)].
Poly OtherPoly(const Face &F, const CornerData &cd, const Iv &vjD) {
  Poly P;
  P.c[0][0][0] = cd.qD - vjD;
  AddLinear(&P, F, cd.g, 1, IvOf(2));
  AddBilinear(&P, F, cd.q, cd.D, 2, IvOf(2));
  AddNormSq(&P, 2, IvOf(-1) * (cd.qD + vjD));
  return P;
}

struct Certifier {
  const Data &data;
  int normal;
  int max_sigma_depth = 4;  // --sigma_depth

  // Per witness, triangle-independent interval data (from exact K values):
  // everything per corner P is linear in P: v_j.D = P.(c x v_j),
  // q.D = P.(c x q), g = q x (P x c) = P (q.c) - c (q.P).
  struct WData {
    Iv q[3], c[3], cq[3], qc;
    std::vector<std::array<Iv, 3>> cv;  // c x v_j
  };
  std::vector<WData> wdata_;
  void Init() {
    const Normal &nm = data.normals[normal];
    for (const Witness &w : nm.w) {
      WData d;
      const KVec &q = nm.L[w.i];
      const KVec cq = Cross(w.c, q);
      for (int a = 0; a < 3; a++) {
        d.q[a] = IvOfK(q[a]);
        d.c[a] = IvOfK(w.c[a]);
        d.cq[a] = IvOfK(cq[a]);
      }
      d.qc = IvOfK(Dot(q, w.c));
      for (const KVec &v : data.V) {
        const KVec cv = Cross(w.c, v);
        d.cv.push_back({IvOfK(cv[0]), IvOfK(cv[1]), IvOfK(cv[2])});
      }
      wdata_.push_back(std::move(d));
    }
  }

  std::vector<std::array<CornerData, 3>> Prepare(const exact5d::TriangleQ &tri) const {
    std::vector<std::array<CornerData, 3>> out(wdata_.size());
    Iv P[3][3];
    for (int c = 0; c < 3; c++) for (int a = 0; a < 3; a++) P[c][a] = IvOfQ(tri[c][a]);
    auto dot = [](const Iv x[3], const Iv y[3]) { return x[0] * y[0] + x[1] * y[1] + x[2] * y[2]; };
    for (size_t k = 0; k < wdata_.size(); k++) {
      const WData &d = wdata_[k];
      for (int c = 0; c < 3; c++) {
        CornerData &cd = out[k][c];
        const Iv *p = P[c];
        // D = P x c
        cd.D[0] = p[1] * d.c[2] - p[2] * d.c[1];
        cd.D[1] = p[2] * d.c[0] - p[0] * d.c[2];
        cd.D[2] = p[0] * d.c[1] - p[1] * d.c[0];
        const Iv qp = dot(d.q, p);
        for (int a = 0; a < 3; a++) {
          cd.q[a] = d.q[a];
          cd.g[a] = p[a] * d.qc - d.c[a] * qp;
        }
        cd.qD = dot(p, d.cq);
        cd.vD.resize(d.cv.size());
        for (size_t j = 0; j < d.cv.size(); j++) cd.vD[j] = dot(p, d.cv[j].data());
      }
    }
    return out;
  }

  // Whether witness k covers the box (all j, all corners); orientation: the
  // witness's d = u x c must point outward, i.e. qD >= vjD at t = 0 (checked
  // by the bounds themselves).
  bool Covers(const std::vector<std::array<CornerData, 3>> &cds, int k, const Face &F, double s1lo, double s1hi,
              double s2lo, double s2hi, double rho, int sign) const {
    const Witness &w = data.normals[normal].w[k];
    for (int c = 0; c < 3; c++) {
      CornerData cd = cds[k][c];
      if (sign < 0) {
        // Use -c: negate D-dependent quantities.
        for (int a = 0; a < 3; a++) { cd.g[a] = IvOf(-1) * cd.g[a]; cd.D[a] = IvOf(-1) * cd.D[a]; }
        cd.qD = IvOf(-1) * cd.qD;
        for (Iv &x : cd.vD) x = IvOf(-1) * x;
      }
      if (BernsteinLower(TiedPoly(F, cd), s1lo, s1hi, s2lo, s2hi, rho) <= 0) return false;
      for (size_t j = 0; j < cd.vD.size(); j++) {
        if (std::find(w.tied.begin(), w.tied.end(), (int)j) != w.tied.end()) continue;
        // Quick accept: the support gap (constant term) dominates the t terms,
        // bounded crudely: |sigma|_inf <= 1, |sigma|^2 <= 3.
        const Iv A = cd.qD - cd.vD[j];
        double gsum = 0, qsum = 0, dsum = 0;
        for (int a = 0; a < 3; a++) {
          gsum += std::max(std::abs(cd.g[a].lo), std::abs(cd.g[a].hi));
          qsum += std::max(std::abs(cd.q[a].lo), std::abs(cd.q[a].hi));
          dsum += std::max(std::abs(cd.D[a].lo), std::abs(cd.D[a].hi));
        }
        const Iv qv = cd.qD + cd.vD[j];
        const double c2 = 2 * qsum * dsum + 3 * std::max(std::abs(qv.lo), std::abs(qv.hi));
        if (A.lo - rho * 2 * gsum * 1.0000001 - rho * rho * c2 * 1.0000001 > 0) continue;
        if (BernsteinLower(OtherPoly(F, cd, cd.vD[j]), s1lo, s1hi, s2lo, s2hi, rho) <= 0) return false;
      }
    }
    return true;
  }

  // Midpoint value of the first-order term (screening).
  double Screen(const std::vector<std::array<CornerData, 3>> &cds, int k, const Face &F, double s1, double s2,
                int sign) const {
    double m = INFINITY;
    for (int c = 0; c < 3; c++) {
      const CornerData &cd = cds[k][c];
      double sigma[3];
      sigma[F.a1] = s1; sigma[F.a2] = s2; sigma[F.f] = F.sg;
      double v = 0;
      for (int a = 0; a < 3; a++) v += sigma[a] * 0.5 * (cd.g[a].lo + cd.g[a].hi);
      m = std::min(m, sign * v);
    }
    return m;
  }

  // Oriented witnesses valid on the triangle: q a support point in direction
  // d at every corner (non-tied gaps positive there).
  std::vector<int> valid_;  // signed (k + 1)
  void FindValid(const std::vector<std::array<CornerData, 3>> &cds) {
    valid_.clear();
    const Normal &nm = data.normals[normal];
    for (size_t k = 0; k < cds.size(); k++) {
      for (int sign : {1, -1}) {
        bool ok = true;
        for (int c = 0; c < 3 && ok; c++) {
          for (size_t j = 0; j < cds[k][c].vD.size() && ok; j++) {
            if (std::find(nm.w[k].tied.begin(), nm.w[k].tied.end(), (int)j) != nm.w[k].tied.end()) continue;
            const Iv gap = cds[k][c].qD - cds[k][c].vD[j];
            ok = sign > 0 ? gap.lo > 0 : gap.hi < 0;
          }
        }
        if (ok) valid_.push_back(sign * (int)(k + 1));
      }
    }
  }

  bool CoverBox(const std::vector<std::array<CornerData, 3>> &cds, const Face &F, double s1lo, double s1hi,
                double s2lo, double s2hi, double rho, int depth, int64_t *boxes) const {
    std::vector<std::pair<double, int>> order;
    for (int sk : valid_) {
      const int k = std::abs(sk) - 1;
      for (int sign : {sk > 0 ? 1 : -1}) {
        const double v = Screen(cds, k, F, 0.5 * (s1lo + s1hi), 0.5 * (s2lo + s2hi), sign);
        if (v > 0) order.push_back({v, sign * (k + 1)});
      }
    }
    std::sort(order.rbegin(), order.rend());
    for (size_t r = 0; r < order.size() && r < 6; r++) {
      const int sk = order[r].second, k = std::abs(sk) - 1, sign = sk > 0 ? 1 : -1;
      if (Covers(cds, k, F, s1lo, s1hi, s2lo, s2hi, rho, sign)) {
        (*boxes)++;
        return true;
      }
    }
    if (depth >= max_sigma_depth) return false;
    const double m1 = 0.5 * (s1lo + s1hi), m2 = 0.5 * (s2lo + s2hi);
    return CoverBox(cds, F, s1lo, m1, s2lo, m2, rho, depth + 1, boxes) &&
           CoverBox(cds, F, m1, s1hi, s2lo, m2, rho, depth + 1, boxes) &&
           CoverBox(cds, F, s1lo, m1, m2, s2hi, rho, depth + 1, boxes) &&
           CoverBox(cds, F, m1, s1hi, m2, s2hi, rho, depth + 1, boxes);
  }

  // Double-precision screen at the centroid view: the first-order cage margin
  // min over sigma of max over oriented witnesses (q a support point of K in
  // direction d) of 2 (sigma x q).d / |sigma||d|. <= 0: no tie tube here.
  double ScreenMargin(const exact5d::TriangleQ &tri) const {
    const Normal &nm = data.normals[normal];
    double u[3];
    for (int a = 0; a < 3; a++) u[a] = (tri[0][a] + tri[1][a] + tri[2][a]).ToDouble();
    auto f3 = [](const KVec &v, double out[3]) { for (int a = 0; a < 3; a++) out[a] = IvOfK(v[a]).lo; };
    std::vector<std::array<double, 3>> Vd(data.V.size());
    for (size_t j = 0; j < data.V.size(); j++) f3(data.V[j], Vd[j].data());
    struct W { double g[3]; };
    std::vector<W> ws;
    for (const Witness &w : nm.w) {
      double q[3], c[3];
      f3(nm.L[w.i], q);
      f3(w.c, c);
      double d[3] = {u[1] * c[2] - u[2] * c[1], u[2] * c[0] - u[0] * c[2], u[0] * c[1] - u[1] * c[0]};
      const double dn = std::sqrt(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
      for (int sign : {1, -1}) {
        double dd[3] = {sign * d[0] / dn, sign * d[1] / dn, sign * d[2] / dn};
        const double qd = q[0] * dd[0] + q[1] * dd[1] + q[2] * dd[2];
        bool support = true;
        for (const auto &v : Vd) support = support && v[0] * dd[0] + v[1] * dd[1] + v[2] * dd[2] <= qd + 1e-9;
        if (!support) continue;
        W x;
        // (sigma x q).d = sigma.(q x d)
        x.g[0] = q[1] * dd[2] - q[2] * dd[1]; x.g[1] = q[2] * dd[0] - q[0] * dd[2]; x.g[2] = q[0] * dd[1] - q[1] * dd[0];
        ws.push_back(x);
      }
    }
    double m = INFINITY;
    for (int k = 0; k < 2000; k++) {
      const double z = 1 - (k + 0.5) / 1000.0, r = std::sqrt(std::max(0.0, 1 - z * z)), ph = k * 2.39996322972865332;
      const double sg[3] = {r * std::cos(ph), r * std::sin(ph), z};
      double best = -INFINITY;
      for (const W &x : ws) best = std::max(best, 2 * (sg[0] * x.g[0] + sg[1] * x.g[1] + sg[2] * x.g[2]));
      m = std::min(m, best);
    }
    return m;
  }

  // The smallest (over the corners and centroid) of the largest protrusion of
  // L's shadow outside K's: when it is clearly positive, M(u) is not near a
  // tie anywhere on the node and the 5D search needs no tie tube there.
  double MinProtrusion(const exact5d::TriangleQ &tri) const {
    const Normal &nm = data.normals[normal];
    auto f3 = [](const KVec &v) { std::array<double, 3> o; for (int a = 0; a < 3; a++) o[a] = IvOfK(v[a]).lo; return o; };
    std::vector<std::array<double, 3>> Vd, Ld;
    for (const KVec &v : data.V) Vd.push_back(f3(v));
    for (const KVec &v : nm.L) Ld.push_back(f3(v));
    double best = INFINITY;
    for (int s = 0; s < 4; s++) {
      double u[3];
      for (int a = 0; a < 3; a++) {
        u[a] = s < 3 ? tri[s][a].ToDouble() : (tri[0][a] + tri[1][a] + tri[2][a]).ToDouble();
      }
      const double un = std::sqrt(u[0] * u[0] + u[1] * u[1] + u[2] * u[2]);
      for (double &x : u) x /= un;
      // Support function check over 720 directions in the view plane.
      double e1[3] = {u[1], -u[0], 0};
      double n1 = std::sqrt(e1[0] * e1[0] + e1[1] * e1[1]);
      if (n1 < 1e-9) { e1[0] = 1; e1[1] = 0; n1 = 1; }
      for (double &x : e1) x /= n1;
      const double e2[3] = {u[1] * e1[2] - u[2] * e1[1], u[2] * e1[0] - u[0] * e1[2], u[0] * e1[1] - u[1] * e1[0]};
      double prot = -INFINITY;
      for (int k = 0; k < 720; k++) {
        const double ang = k * M_PI / 360, d[3] = {std::cos(ang) * e1[0] + std::sin(ang) * e2[0],
                                                    std::cos(ang) * e1[1] + std::sin(ang) * e2[1],
                                                    std::cos(ang) * e1[2] + std::sin(ang) * e2[2]};
        double hk = -INFINITY, hl = -INFINITY;
        for (const auto &v : Vd) hk = std::max(hk, v[0] * d[0] + v[1] * d[1] + v[2] * d[2]);
        for (const auto &v : Ld) hl = std::max(hl, v[0] * d[0] + v[1] * d[1] + v[2] * d[2]);
        prot = std::max(prot, hl - hk);
      }
      best = std::min(best, prot);
    }
    return best;
  }

  // Whether radius rho is certified on the triangle.
  bool Certify(const exact5d::TriangleQ &tri, double rho, int64_t *boxes) {
    const auto cds = Prepare(tri);
    FindValid(cds);
    if (valid_.empty()) return false;
    for (int f = 0; f < 3; f++) {
      for (double sg : {1.0, -1.0}) {
        Face F{f, f == 0 ? 1 : 0, f == 2 ? 1 : 2, sg};
        if (!CoverBox(cds, F, -1, 1, -1, 1, rho, 0, boxes)) return false;
      }
    }
    return true;
  }
};

}  // namespace

int main(int argc, char **argv) {
  std::fesetround(FE_TONEAREST);
  InitConstants();
  std::string data_file = "dh_tie_data.txt", trees_dir = "/mnt/nopertdata/work/dh/work/trees_r1",
              bdd = "codebdd.json", out_dir = "/mnt/nopertdata/work/dh/work/tie";
  std::vector<int> normals, tris;
  int max_depth = 8, threads = 60, start_depth = 3;
  bool debug = false;
  double far_protrusion = 0.002;
  std::vector<std::array<double, 4>> caps;  // unit center, radius
  int sigma_depth = 4;
  Q min_rho(1, 1024);
  auto ParseList = [](const std::string &s) {
    std::vector<int> v;
    std::stringstream ss(s);
    std::string t;
    while (std::getline(ss, t, ',')) v.push_back(std::stoi(t));
    return v;
  };
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--data") data_file = next();
    else if (a == "--normals") normals = ParseList(next());
    else if (a == "--t") tris = ParseList(next());
    else if (a == "--trees_dir") trees_dir = next();
    else if (a == "--bdd") bdd = next();
    else if (a == "--out_dir") out_dir = next();
    else if (a == "--max_depth") max_depth = std::stoi(next());
    else if (a == "--min_rho") min_rho = Q(std::string_view(next()));
    else if (a == "--threads") threads = std::stoi(next());
    else if (a == "--start_depth") start_depth = std::stoi(next());
    else if (a == "--debug") debug = true;
    else if (a == "--far_protrusion") far_protrusion = std::stod(next());
    else if (a == "--cap") {
      std::array<double, 4> c;
      CHECK(std::sscanf(next().c_str(), "%lf,%lf,%lf,%lf", &c[0], &c[1], &c[2], &c[3]) == 4);
      const double n = std::sqrt(c[0] * c[0] + c[1] * c[1] + c[2] * c[2]);
      for (int a = 0; a < 3; a++) c[a] /= n;
      caps.push_back(c);
    }
    else if (a == "--sigma_depth") sigma_depth = std::stoi(next());
    else LOG(FATAL) << "unknown argument " << a;
  }
  const Data data = LoadData(data_file);
  printf("loaded %zu vertices, %zu normals (exact facts re-verified)\n", data.V.size(), data.normals.size());
  const auto atlas = tubeatlas5d::TubeAtlas::Load(trees_dir, bdd);
  if (normals.empty()) for (size_t n = 0; n < data.normals.size(); n++) normals.push_back(n);
  if (tris.empty()) for (int t = 0; t < atlas.NumTriangles(); t++) tris.push_back(t);
  std::filesystem::create_directories(out_dir);

  // Jobs: (normal, triangle). Each writes out_dir/n<n>_t<t>.txt: "path rho" per node
  // (rho 0 = uncertified leaf at max depth).
  struct Job { int n, t; };
  std::vector<Job> jobs;
  for (int n : normals) for (int t : tris) jobs.push_back({n, t});
  std::atomic<size_t> next_job{0};
  std::mutex mu;
  auto worker = [&]() {
    for (;;) {
      const size_t k = next_job++;
      if (k >= jobs.size()) return;
      const Job job = jobs[k];
      Certifier cert{data, job.n};
      cert.max_sigma_depth = sigma_depth;
      cert.Init();
      std::string out;
      int64_t boxes = 0, nodes = 0, failed = 0;
      double min_rho_seen = 1;
      int64_t skipped = 0;
      std::function<void(const exact5d::TriangleQ &, const std::string &)> rec =
          [&](const exact5d::TriangleQ &tri, const std::string &path) {
        nodes++;
        // Triangles inside a cap are left to the cap theorems ("C"), whose
        // rotation radius covers the ties there.
        {
          bool in_any = false;
          for (const auto &cap : caps) {
            bool in = true;
            for (int k = 0; k < 3 && in; k++) {
              double v[3], n = 0;
              for (int a = 0; a < 3; a++) { v[a] = tri[k][a].ToDouble(); n += v[a] * v[a]; }
              n = std::sqrt(n);
              double dt = 0;
              for (int a = 0; a < 3; a++) dt += v[a] / n * cap[a];
              in = std::acos(std::clamp(dt, -1.0, 1.0)) <= cap[3];
            }
            in_any = in_any || in;
          }
          if (in_any) {
            out += std::format("{} C\n", path.empty() ? "." : path);
            return;
          }
        }
        if ((int)path.size() >= start_depth) {
          if (cert.MinProtrusion(tri) > far_protrusion) {
            out += std::format("{} F\n", path);
            skipped++;
            return;
          }
          const double m = cert.ScreenMargin(tri);
          if (debug && (int)path.size() == max_depth) {
            int64_t b2 = 0;
            const auto cds = cert.Prepare(tri);
            cert.FindValid(cds);
            std::string rs;
            for (Q r(1, 8); !(r < Q(1, 4096)); r = r / Q(2)) rs += cert.Certify(tri, r.ToDouble(), &b2) ? "+" : "-";
            printf("debug %s: screen margin %.4g, valid witnesses %zu, rho 1/8..1/4096: %s\n", path.c_str(), m,
                   cert.valid_.size(), rs.c_str());
          }
          if (!(m > 0)) {
            out += std::format("{} N\n", path);
            skipped++;
            return;
          }
          // Binary search over the ladder 1/8, 1/16, ..., min_rho (certification
          // is monotone in rho).
          std::vector<Q> ladder;
          for (Q r(1, 8); !(r < min_rho); r = r / Q(2)) ladder.push_back(r);
          int lo = (int)ladder.size(), hi = -1;  // ladder[lo] certified (lo = size: none yet)
          int a = 0, b = (int)ladder.size() - 1;
          if (cert.Certify(tri, ladder[b].ToDouble(), &boxes)) {
            lo = b;
            while (a < lo) {
              const int mid = (a + lo) / 2;
              if (cert.Certify(tri, ladder[mid].ToDouble(), &boxes)) lo = mid;
              else a = mid + 1;
            }
          }
          (void)hi;
          if (lo < (int)ladder.size()) {
            out += std::format("{} {}\n", path, ladder[lo].ToString());
            min_rho_seen = std::min(min_rho_seen, ladder[lo].ToDouble());
            return;
          }
          if ((int)path.size() >= max_depth) {
            double c[3];
            for (int a = 0; a < 3; a++) c[a] = (tri[0][a] + tri[1][a] + tri[2][a]).ToDouble();
            const double n = std::sqrt(c[0] * c[0] + c[1] * c[1] + c[2] * c[2]);
            out += std::format("{} 0 {:.6f} {:.6f} {:.6f}\n", path, c[0] / n, c[1] / n, c[2] / n);
            failed++;
            return;
          }
        }
        out += std::format("{} S\n", path.empty() ? "." : path);
        for (int c = 0; c < 4; c++) rec(geom5d::SplitTriangle(tri, c), path + (char)('0' + c));
      };
      rec(atlas.Triangle(job.t), "");
      {
        std::ofstream f(std::format("{}/n{}_t{}.txt", out_dir, job.n, job.t));
        f << out;
      }
      std::lock_guard<std::mutex> l(mu);
      printf("normal %d triangle %d: %lld nodes, %lld sigma boxes, %lld uncertified, %lld no cage, min rho %.4g\n",
             job.n, job.t, (long long)nodes, (long long)boxes, (long long)failed, (long long)skipped, min_rho_seen);
      fflush(stdout);
    }
  };
  std::vector<std::thread> ts;
  for (int i = 0; i < threads; i++) ts.emplace_back(worker);
  for (auto &t : ts) t.join();
  return 0;
}
