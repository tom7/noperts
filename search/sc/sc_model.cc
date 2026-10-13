// sc_model: the exact model of the snub cube for the search (codebdd
// --model_file), and its symmetry table.
//
// The snub cube, in Wikipedia's chirality, is the set of even permutations of
// (+-1, +-1/t, +-t) with an even number of plus signs and odd permutations
// with an odd number of plus signs, t the tribonacci constant (the real root
// of t^3 = t^2 + t + 1). Scaled by t it is the orbit of (t, 1, -t^2) under
// the octahedral rotation group O (the 24 signed permutation matrices with
// determinant 1). The coordinate axes are its 4-fold axes.
//
// Vertex order (rotation-major C4 about z): vertex 6 k + s is Rz(pi/2)^k
// applied to seed s, where the seeds are the images of (t, 1, -t^2) under six
// representatives of the cosets O / C4 (sorted by decreasing z, then y).
//
// The rational model is the orbit of one rational seed: the unit seed scaled
// by 1 - 10^-9 and rounded to a multiple of 2^-52 in each coordinate, moved
// by the exact (integer) matrices of O. So it is exactly O-symmetric (the
// squares are exactly planar), within 3e-16 of the exact solid.
//
// Output (sc_model.txt):
//   name snubcube
//   vertex i x y z           24 lines: the exact solid at circumradius
//                            1 - 10^-9, 40 decimals
//   rational_vertex i p/q .. 24 lines: the rational model
//   face i j k ...           the 38 faces (6 squares, 32 triangles), counter-
//                            clockwise seen from outside
//   view_triangle ...        the Oh chamber 0 <= u1 <= u0 <= u2 on the plane
//                            x + y + z = 1: corners (0,0,1), (1/2,0,1/2),
//                            (1/3,1/3,1/3)
//   ustar x y z              the degenerate views in the view triangle (see
//                            notes/SNUB-CUBE.md in nopert229): e_a x p for
//                            the vertices p with |p_a| = t / r (the middle
//                            coordinate), moved into the chamber (40 decimals)
// and symmetry_neighbors.h: the 23 nontrivial rotations of O, exact (the
// prune removes boxes where trace(R g) > trace R).
//
// Usage: sc_model.exe [out=sc_model.txt] [header=symmetry_neighbors.h]

#include <algorithm>
#include <array>
#include <cstdio>
#include <format>
#include <fstream>
#include <string>
#include <vector>

#include "base/logging.h"
#include "bignum/big.h"
#include "bignum/big-overloads.h"

namespace {

using Q = BigRat;
using V = std::array<Q, 3>;
using M = std::array<std::array<int, 3>, 3>;

// 10^-digits-accurate rational approximations.
Q Abs(const Q &x) { return x < Q(0) ? Q(0) - x : x; }

// The tribonacci constant to within 10^-100 (Newton from 1.84).
Q Tribonacci() {
  Q t(184, 100);
  const Q eps(BigInt(1), BigInt::Pow(BigInt(10), 100));
  for (int i = 0; i < 200; i++) {
    const Q f = t * t * t - t * t - t - Q(1), df = Q(3) * t * t - Q(2) * t - Q(1);
    const Q step = f / df;
    // Keep the numbers small: round to 10^-110.
    const BigInt scale = BigInt::Pow(BigInt(10), 110);
    auto [n, d] = ((t - step) * Q(scale)).Parts();
    t = Q(BigInt::DivFloor(n, d), scale);
    if (Abs(step) < eps) break;
  }
  return t;
}

// sqrt(x) to within 10^-100 (Newton, from above).
Q Sqrt(const Q &x) {
  Q y(2);
  while (y * y < x) y = y * Q(2);
  const BigInt scale = BigInt::Pow(BigInt(10), 110);
  for (int i = 0; i < 400; i++) {
    const Q ny = (y + x / y) / Q(2);
    auto [n, d] = (ny * Q(scale)).Parts();
    const Q r(BigInt::DivFloor(n, d) + BigInt(1), scale);
    if (Abs(r - y) < Q(BigInt(1), BigInt::Pow(BigInt(10), 105))) { y = r; break; }
    y = r;
  }
  return y;
}

std::string Decimal(const Q &x, int digits) {
  const BigInt scale = BigInt::Pow(BigInt(10), digits);
  auto [n, d] = (Abs(x) * Q(scale) + Q(1, 2)).Parts();
  std::string s = BigInt::DivFloor(n, d).ToString();
  while ((int)s.size() <= digits) s = "0" + s;
  s.insert(s.size() - digits, ".");
  return (x < Q(0) ? "-" : "") + s;
}

std::vector<M> Octahedral() {
  std::vector<M> G;
  const int perms[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};
  const int psign[6] = {1, -1, -1, 1, 1, -1};
  for (int p = 0; p < 6; p++)
    for (int s = 0; s < 8; s++) {
      const int sg[3] = {s & 1 ? -1 : 1, s & 2 ? -1 : 1, s & 4 ? -1 : 1};
      if (psign[p] * sg[0] * sg[1] * sg[2] != 1) continue;
      M m{};
      for (int r = 0; r < 3; r++) m[r][perms[p][r]] = sg[r];
      G.push_back(m);
    }
  CHECK(G.size() == 24);
  return G;
}

V Apply(const M &m, const V &v) {
  V r;
  for (int i = 0; i < 3; i++) r[i] = Q(m[i][0]) * v[0] + Q(m[i][1]) * v[1] + Q(m[i][2]) * v[2];
  return r;
}
M Mul(const M &a, const M &b) {
  M r{};
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++)
      for (int k = 0; k < 3; k++) r[i][j] += a[i][k] * b[k][j];
  return r;
}
Q Dot(const V &a, const V &b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
V Sub(const V &a, const V &b) { return {a[0] - b[0], a[1] - b[1], a[2] - b[2]}; }
V Cross(const V &a, const V &b) {
  return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]};
}
bool Eq(const V &a, const V &b) { return a[0] == b[0] && a[1] == b[1] && a[2] == b[2]; }

Q RoundTo(const Q &x, const BigInt &scale) {
  auto [n, d] = (x * Q(scale) + Q(1, 2)).Parts();
  return Q(BigInt::DivFloor(n, d), scale);
}

}  // namespace

int main(int argc, char **argv) {
  const std::string out_file = argc > 1 ? argv[1] : "sc_model.txt";
  const std::string header_file = argc > 2 ? argv[2] : "symmetry_neighbors.h";

  const Q t = Tribonacci();
  const V seed0{t, Q(1), Q(0) - t * t};
  const Q r = Sqrt(Dot(seed0, seed0));
  const std::vector<M> G = Octahedral();
  const M rz{{{0, -1, 0}, {1, 0, 0}, {0, 0, 1}}};  // Rz(pi/2)
  M rzk[4];
  rzk[0] = {{{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}};
  for (int k = 1; k < 4; k++) rzk[k] = Mul(rz, rzk[k - 1]);

  // Coset representatives of O / C4 (g ~ Rz^k g): the six seeds.
  std::vector<M> reps;
  for (const M &g : G) {
    bool seen = false;
    for (const M &h : reps)
      for (int k = 0; k < 4; k++) seen = seen || Mul(rzk[k], h) == g;
    if (!seen) reps.push_back(g);
  }
  CHECK(reps.size() == 6);
  // Sort the seeds by decreasing z, then y (of the exact images).
  std::sort(reps.begin(), reps.end(), [&](const M &a, const M &b) {
    const V pa = Apply(a, seed0), pb = Apply(b, seed0);
    if (!(pa[2] == pb[2])) return pb[2] < pa[2];
    return pb[1] < pa[1];
  });
  std::vector<M> slot(24);
  for (int k = 0; k < 4; k++)
    for (int s = 0; s < 6; s++) slot[6 * k + s] = Mul(rzk[k], reps[s]);

  // Exact (unit) and rational models.
  const BigInt scale52 = BigInt::Pow(BigInt(2), 52);
  const Q shrink = Q(1) - Q(BigInt(1), BigInt::Pow(BigInt(10), 9));
  V qseed;
  for (int i = 0; i < 3; i++) qseed[i] = RoundTo(seed0[i] / r * shrink, scale52);
  std::vector<V> exact(24), rat(24);
  for (int i = 0; i < 24; i++) {
    const V e = Apply(slot[i], seed0);
    for (int a = 0; a < 3; a++) exact[i][a] = e[a] / r * shrink;
    rat[i] = Apply(slot[i], qseed);
  }
  for (int i = 0; i < 24; i++)
    for (int j = i + 1; j < 24; j++) CHECK(!Eq(rat[i], rat[j])) << "slots " << i << " " << j;
  // Distance from the exact solid.
  double maxerr = 0;
  for (int i = 0; i < 24; i++) {
    const V d = Sub(rat[i], exact[i]);
    maxerr = std::max(maxerr, std::sqrt(Dot(d, d).ToDouble()));
  }
  CHECK(maxerr < 3e-16) << maxerr;

  // Faces of the rational model: planes through three vertices with every
  // vertex on one side (exact).
  std::vector<std::vector<int>> faces;
  for (int a = 0; a < 24; a++)
    for (int b = a + 1; b < 24; b++)
      for (int c = b + 1; c < 24; c++) {
        V n = Cross(Sub(rat[b], rat[a]), Sub(rat[c], rat[a]));
        if (n[0] == Q(0) && n[1] == Q(0) && n[2] == Q(0)) continue;
        bool pos = false, neg = false;
        std::vector<int> on;
        for (int j = 0; j < 24; j++) {
          const Q s = Dot(n, Sub(rat[j], rat[a]));
          if (s == Q(0)) on.push_back(j);
          else if (Q(0) < s) pos = true;
          else neg = true;
        }
        if (pos && neg) continue;
        if (on[0] != a || on[1] != b || on[2] != c) continue;  // count each face once
        if (pos) n = {Q(0) - n[0], Q(0) - n[1], Q(0) - n[2]};  // outward
        // Order counterclockwise seen from outside (around the centroid).
        V cen{Q(0), Q(0), Q(0)};
        for (int j : on) for (int k = 0; k < 3; k++) cen[k] = cen[k] + rat[j][k];
        for (int k = 0; k < 3; k++) cen[k] = cen[k] / Q((int)on.size());
        const V e1 = Sub(rat[on[0]], cen), e2 = Cross(n, e1);
        std::sort(on.begin() + 1, on.end(), [&](int x, int y) {
          const V px = Sub(rat[x], cen), py = Sub(rat[y], cen);
          const double ax = std::atan2(Dot(px, e2).ToDouble(), Dot(px, e1).ToDouble());
          const double ay = std::atan2(Dot(py, e2).ToDouble(), Dot(py, e1).ToDouble());
          return (ax < 0 ? ax + 2 * M_PI : ax) < (ay < 0 ? ay + 2 * M_PI : ay);
        });
        faces.push_back(on);
      }
  int squares = 0, triangles = 0;
  for (const auto &f : faces) (f.size() == 4 ? squares : triangles)++;
  CHECK(squares == 6 && triangles == 32) << squares << " squares, " << triangles << " triangles";

  // The degenerate views: e_a x p for a coordinate axis a and a vertex p
  // whose coordinate along a has the middle magnitude (t / r): at e_a x p the
  // width across a is critical and the first-order margin vanishes (the
  // other critical family, |p_a| = 1 / r, keeps a positive margin). Their
  // images under O and -1 that lie in the chamber 0 <= u1 <= u0 <= u2.
  std::vector<V> ustar;
  const Q mid = t / r * shrink;
  for (const V &p : exact) {
    for (int a = 0; a < 3; a++) {
      if (!(Abs(p[a]) == mid)) continue;
      V ea{Q(0), Q(0), Q(0)};
      ea[a] = Q(1);
      const V u0 = Cross(ea, p);
      for (const M &g : G)
        for (int sg : {1, -1}) {
          V u = Apply(g, u0);
          if (sg < 0) u = {Q(0) - u[0], Q(0) - u[1], Q(0) - u[2]};
          if (!(Q(0) <= u[1] && u[1] <= u[0] && u[0] <= u[2])) continue;
          // Compare directions (u is not normalized).
          bool dup = false;
          for (const V &w : ustar) {
            const V c = Cross(w, u);
            dup = dup || (c[0] == Q(0) && c[1] == Q(0) && c[2] == Q(0) && Q(0) < Dot(w, u));
          }
          if (!dup) ustar.push_back(u);
        }
    }
  }

  std::ofstream out(out_file);
  out << "name snubcube\n";
  out << "# The O-orbit of (t, 1, -t^2) (t^3 = t^2 + t + 1; Wikipedia's chirality), circumradius 1 - 1e-9;\n";
  out << "# vertex 6 k + s = Rz(pi/2)^k seed s. The rational model is the O-orbit of one rational seed\n";
  out << std::format("# (exactly O-symmetric), within {:.2e} of the exact solid.\n", maxerr);
  for (int i = 0; i < 24; i++)
    out << "vertex " << i << " " << Decimal(exact[i][0], 40) << " " << Decimal(exact[i][1], 40) << " "
        << Decimal(exact[i][2], 40) << "\n";
  for (int i = 0; i < 24; i++)
    out << "rational_vertex " << i << " " << rat[i][0].ToString() << " " << rat[i][1].ToString() << " "
        << rat[i][2].ToString() << "\n";
  for (const auto &f : faces) {
    out << "face";
    for (int j : f) out << " " << j;
    out << "\n";
  }
  out << "view_triangle 0/1 0/1 1/1 1/2 0/1 1/2 1/3 1/3 1/3\n";
  for (const V &u : ustar) {
    const Q n = Sqrt(Dot(u, u));
    out << "ustar " << Decimal(u[0] / n, 40) << " " << Decimal(u[1] / n, 40) << " " << Decimal(u[2] / n, 40) << "\n";
  }
  out.close();

  std::ofstream h(header_file);
  h << "// Generated by sc_model.exe: the 23 nontrivial rotations of the octahedral\n"
       "// group O (signed permutation matrices), exact (denominator 1, no rounding\n"
       "// allowance). The cell prune (exact5d::IcoPruneValid) removes boxes where\n"
       "// trace(R g) > trace(R).\n"
       "#ifndef _NOPERT_SYMMETRY_NEIGHBORS_H\n#define _NOPERT_SYMMETRY_NEIGHBORS_H\n\n#include <cstdint>\n\n"
       "inline constexpr int NUM_SYMMETRY_NEIGHBORS = 23;\n"
       "inline constexpr int64_t SYMMETRY_NEIGHBOR_DENOM = 1;\n"
       "// The entries are exact: the prune needs a strictly positive lower bound.\n"
       "inline constexpr bool SYMMETRY_NEIGHBOR_EXACT = true;\n"
       "// Row-major numerators.\n"
       "inline constexpr int64_t SYMMETRY_NEIGHBOR_NUM[NUM_SYMMETRY_NEIGHBORS][9] = {\n";
  for (const M &g : G) {
    if (g[0][0] == 1 && g[1][1] == 1 && g[2][2] == 1) continue;
    h << "  {";
    for (int i = 0; i < 9; i++) h << g[i / 3][i % 3] << (i < 8 ? ", " : "");
    h << "},\n";
  }
  h << "};\n\n#endif\n";

  printf("snub cube: t = %s\n  24 vertices, %d faces (%d squares, %d triangles); rational model within %.2e\n",
         Decimal(t, 20).c_str(), (int)faces.size(), squares, triangles, maxerr);
  printf("  %d degenerate views u* in the view triangle:\n", (int)ustar.size());
  for (const V &u : ustar) {
    const double n = std::sqrt(Dot(u, u).ToDouble());
    printf("    (%.12f, %.12f, %.12f)\n", u[0].ToDouble() / n, u[1].ToDouble() / n, u[2].ToDouble() / n);
  }
  return 0;
}
