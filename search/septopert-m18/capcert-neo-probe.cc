// capcert-neo-probe: pointwise test of witnesses at blown-up poses of M18 (float).
// Apex frame, units of REPORT.md: O=0, A=81ex, B=81ey, C=81ez ... For a pose (outer tilt (a,b) so
// u ~ (-a,-b,1); Cayley vector w) it computes
//   width: max over directions of inner width - outer width,
//   clear: -min_t max_e (h_in(n_e) - h_e + n_e.t), the true clearance deficit (LP over outer edges).
// Modes sample blown-up neighbourhoods and print the worst of width/scale and clear/scale.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <string>
#include <thread>
#include <vector>
#include <mutex>
#include <functional>
using namespace std;
using V3 = array<double, 3>;
static const V3 VV[7] = {{81, 0, 0}, {0, 81, 0}, {0, 0, 81}, {22, 64, 64}, {64, 22, 64}, {64, 64, 22}, {0, 0, 0}};
// indices as the model: 0=A 1=B 2=C 3=v3 4=v4 5=E 6=O
static const char *NM[7] = {"A", "B", "C", "v3", "v4", "E", "O"};
static double dot(V3 a, V3 b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
static V3 cross(V3 a, V3 b) { return {a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]}; }
static V3 nrm(V3 a) { double n = sqrt(dot(a, a)); return {a[0] / n, a[1] / n, a[2] / n}; }
struct Res { double width, clear; int wk = -1, wkp = -1, wa = -1, wb = -1; };
struct Pt { double x, y; };
static V3 rot(V3 w, V3 v) {
  double ww = dot(w, w), D = 1 + ww, wv = dot(w, v);
  V3 c = cross(w, v), r;
  for (int i = 0; i < 3; i++) r[i] = ((1 - ww) * v[i] + 2 * w[i] * wv + 2 * c[i]) / D;
  return r;
}
static Res eval(V3 u, V3 w) {
  V3 un = nrm(u);
  V3 h1 = nrm(cross(un, V3{0.3, 1, 0})), h2 = cross(un, h1);
  Pt po[7], pi[7];
  for (int i = 0; i < 7; i++) {
    po[i] = {dot(VV[i], h1), dot(VV[i], h2)};
    V3 r = rot(w, VV[i]);
    pi[i] = {dot(r, h1), dot(r, h2)};
  }
  // Width: directions normal to chords of outer and inner point sets.
  Res res{-1e300, 1e300};
  auto G = [&](double dx, double dy, int a, int b) {
    double n = hypot(dx, dy);
    if (n < 1e-12) return;
    dx /= n; dy /= n;
    double mxo = -1e300, mno = 1e300, mxi = -1e300, mni = 1e300; int k = -1, kp = -1;
    for (int i = 0; i < 7; i++) {
      double o = po[i].x * dx + po[i].y * dy, q = pi[i].x * dx + pi[i].y * dy;
      mxo = max(mxo, o); mno = min(mno, o);
      if (q > mxi) { mxi = q; k = i; }
      if (q < mni) { mni = q; kp = i; }
    }
    double g = (mxi - mni) - (mxo - mno);
    if (g > res.width) { res.width = g; res.wk = k; res.wkp = kp; res.wa = a; res.wb = b; }
  };
  for (int i = 0; i < 7; i++)
    for (int j = i + 1; j < 7; j++) {
      G(-(po[j].y - po[i].y), po[j].x - po[i].x, i, j);
      G(-(pi[j].y - pi[i].y), pi[j].x - pi[i].x, 10 + i, 10 + j);
    }
  // Outer hull (strict) edges.
  vector<int> idx(7);
  for (int i = 0; i < 7; i++) idx[i] = i;
  sort(idx.begin(), idx.end(), [&](int a, int b) { return make_pair(po[a].x, po[a].y) < make_pair(po[b].x, po[b].y); });
  auto cr = [&](int o, int a, int b) { return (po[a].x - po[o].x) * (po[b].y - po[o].y) - (po[a].y - po[o].y) * (po[b].x - po[o].x); };
  vector<int> H;
  for (int pass = 0; pass < 2; pass++) {
    size_t st = H.size();
    for (int i : idx) {
      while (H.size() >= st + 2 && cr(H[H.size() - 2], H.back(), i) <= 0) H.pop_back();
      H.push_back(i);
    }
    H.pop_back();
    reverse(idx.begin(), idx.end());
  }
  int m = H.size();
  vector<array<double, 3>> E;  // nx ny c: constraint value c + n.t <= s
  for (int e = 0; e < m; e++) {
    Pt p = po[H[e]], q = po[H[(e + 1) % m]];
    double nx = q.y - p.y, ny = -(q.x - p.x), n = hypot(nx, ny);
    nx /= n; ny /= n;
    double h = nx * p.x + ny * p.y, hi = -1e300;
    for (int i = 0; i < 7; i++) hi = max(hi, nx * pi[i].x + ny * pi[i].y);
    E.push_back({nx, ny, hi - h});
  }
  // min_t max_e: over balanced triples: value s with sum lam_k (c_k) / sum lam.
  double best = -1e300;
  for (int a = 0; a < m; a++)
    for (int b = a + 1; b < m; b++)
      for (int c = b + 1; c < m; c++) {
        double l0 = E[b][0] * E[c][1] - E[b][1] * E[c][0], l1 = E[c][0] * E[a][1] - E[c][1] * E[a][0],
               l2 = E[a][0] * E[b][1] - E[a][1] * E[b][0];
        if ((l0 >= 0 && l1 >= 0 && l2 >= 0) || (l0 <= 0 && l1 <= 0 && l2 <= 0)) {
          double s = l0 + l1 + l2;
          if (abs(s) < 1e-13) continue;
          best = max(best, (l0 * E[a][2] + l1 * E[b][2] + l2 * E[c][2]) / s);
        }
      }
  res.clear = best;  // >0: no passage; deficit.
  return res;
}
// Pose from tilt (a,b), d=(d1,d2) (a'=a+d1, b'=b+d2), g: w = (-d2/2, d1/2, g).
int main(int argc, char **argv) {
  string mode = argv[1];
  double mu = atof(argv[2]);
  long n = atol(argv[3]);
  double R = argc > 4 ? atof(argv[4]) : 2, S = argc > 5 ? atof(argv[5]) : 4;
  double extra = argc > 6 ? atof(argv[6]) : 0;
  int T = 24;
  mutex mx;
  struct Rec { double v; array<double, 6> p; Res r; };
  vector<Rec> worstW, worstC;
  vector<thread> ts;
  for (int t = 0; t < T; t++) ts.emplace_back([&, t]() {
    mt19937_64 rng(1234 + t);
    uniform_real_distribution<double> U(-1, 1);
    vector<Rec> lw, lc;
    for (long i = 0; i < n / T; i++) {
      array<double, 6> p;
      double a, b, d1, d2, g, sc;
      if (mode == "U") {
        // a,b,d in mu * cube, g in mu^2 S; log-uniform scale of D relative.
        double e = pow(10, -3 * fabs(U(rng)));
        double aa = U(rng), bb = U(rng), m = max(fabs(aa), fabs(bb));
        if (U(rng) > -.5) { aa /= m; bb /= m; }
        a = mu * aa; b = mu * bb;
        d1 = mu * R * e * U(rng); d2 = mu * R * e * U(rng);
        g = mu * mu * S * e * U(rng);
        sc = mu * mu * e;
        p = {aa, bb, d1 / mu, d2 / mu, g / mu / mu, e};
      } else {
        fprintf(stderr, "mode\n"); exit(1);
      }
      V3 u{-a, -b, 1}, w{-d2 / 2, d1 / 2, g};
      Res r = eval(u, w);
      double W = r.width / sc, C = r.clear / sc;
      lw.push_back({W, p, r});
      lc.push_back({C, p, r});
      if (lw.size() > 4000) {
        auto cmp = [](const Rec &x, const Rec &y) { return x.v < y.v; };
        partial_sort(lw.begin(), lw.begin() + 10, lw.end(), cmp); lw.resize(10);
        partial_sort(lc.begin(), lc.begin() + 10, lc.end(), cmp); lc.resize(10);
      }
    }
    lock_guard<mutex> l(mx);
    worstW.insert(worstW.end(), lw.begin(), lw.end());
    worstC.insert(worstC.end(), lc.begin(), lc.end());
  });
  for (auto &t : ts) t.join();
  auto cmp = [](const Rec &x, const Rec &y) { return x.v < y.v; };
  sort(worstW.begin(), worstW.end(), cmp);
  sort(worstC.begin(), worstC.end(), cmp);
  for (int i = 0; i < 12 && i < (int)worstW.size(); i++) {
    auto &q = worstW[i];
    printf("W %.4g (clear %.3g) a %.3f b %.3f d %.4f %.4f g %.4f e %.3g  k %s k' %s dir %d-%d\n", q.v, q.r.clear, q.p[0], q.p[1], q.p[2], q.p[3], q.p[4], q.p[5], NM[q.r.wk], NM[q.r.wkp], q.r.wa, q.r.wb);
  }
  for (int i = 0; i < 6 && i < (int)worstC.size(); i++) {
    auto &q = worstC[i];
    printf("C %.4g (width %.3g) a %.3f b %.3f d %.4f %.4f g %.4f e %.3g\n", q.v, q.r.width, q.p[0], q.p[1], q.p[2], q.p[3], q.p[4], q.p[5]);
  }
}
