// dfwhere: where are a 5D job's deferred leaves? For each df leaf of
// jobs/c<chart>/t<t>.journal: the view (normalized centroid) and its angular
// diameter, the Cayley box (center and half-widths), |w|, and the identity
// tube radius at the view, and the first-order margin m(u) of the identity
// pose at the view (rigidity-margin.h). Leaves with m(u) near 0 (and |w|
// near 0) sit at a point where the first-order margin vanishes: candidates
// for a cap certificate, the one technique the search does not try by
// itself (SEPTOPERT-IMPROVEMENTS.md, to-do 10). Diagnostic only.
//
// Usage: dfwhere.exe --chart C --t T [--every K] [--jobs DIR] [--trees_dir DIR] [--bdd codebdd.json]
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <limits>
#include <vector>
#include <string>
#include "base/logging.h"
#include "geom5d.h"
#include "model.h"
#include "rigidity-margin.h"
#include "rows5d.h"
#include "tubeatlas5d.h"
int main(int argc, char **argv) {
  std::string jobs = "jobs", trees = "trees_r2", bdd = "codebdd.json";
  int chart = 0, t = 0, every = 1;
  for (int i = 1; i < argc; i++) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string { CHECK(i + 1 < argc); return argv[++i]; };
    if (a == "--chart") chart = std::stoi(next());
    else if (a == "--t") t = std::stoi(next());
    else if (a == "--every") every = std::stoi(next());
    else if (a == "--jobs") jobs = next();
    else if (a == "--trees_dir") trees = next();
    else if (a == "--bdd") bdd = next();
    else LOG(FATAL) << "unknown argument " << a;
  }
  auto atlas = tubeatlas5d::TubeAtlas::Load(trees, bdd);
  auto j = rows5d::ReadJournal(jobs + "/c" + std::to_string(chart) + "/t" + std::to_string(t) + ".journal");
  auto [code, tri] = atlas.CodeAndTriangle(t);
  printf("job c%d t%d: code %d triangle %d\n", chart, t, code, tri);
  std::vector<yocto::vec<double, 3>> verts;
  for (size_t v = 0; v < (size_t)NUM_VERTICES; v++) verts.push_back(Vertex(v));
  int n = 0;
  double min_m = std::numeric_limits<double>::infinity();
  yocto::vec<double, 3> min_u{0, 0, 0};
  int near_zero = 0;
  for (const auto &r : j.leaves) {
    if (!std::holds_alternative<rows5d::DeferredLeaf>(r.leaf)) continue;
    if (n++ % every) continue;
    const auto T = rows5d::NodeTriangle(atlas.Triangle(t), r.path);
    const auto B = rows5d::NodeBox(geom5d::RootBox(chart), r.path);
    const auto td = geom5d::ToDouble(T);
    const auto bd = geom5d::ToDouble(B);
    const auto u = yocto::normalize(td.corners[0] + td.corners[1] + td.corners[2]);
    const auto reached = atlas.Walk(t, rows5d::ViewPath(r.path));
    const double m = rigidity::FirstOrderMargin(verts, u, false).m;
    if (m < min_m) { min_m = m; min_u = u; }
    if (m < 1e-6) near_zero++;
    printf("u (%.6f %.6f %.6f) diam %.2e  w (%.5f %.5f %.5f) +- (%.1e %.1e %.1e) |w| %.4f  tube r %.3g  m(u) %.3g\n",
           u.x, u.y, u.z, geom5d::AngularDiameter(td), bd.center.x, bd.center.y, bd.center.z,
           bd.radius.x, bd.radius.y, bd.radius.z, yocto::length(bd.center), reached.r_lower.ToDouble(), m);
  }
  printf("%d deferred; least first-order margin m(u) %.3g; %d with m(u) < 1e-6 (cap candidates)\n",
         n, min_m, near_zero);
  if (near_zero > 0) {
    // The rotation axes w (unit) with f_u(w) ~ 0 at the least-margin view: the
    // directions in which the first-order cage is degenerate, i.e. the
    // weight-1 directions of a cap's blow-up (the others get weight 2).
    const auto cons = rigidity::SilhouetteConstraints(verts, min_u, false);
    const int N = 20000;
    double fmax = 0;
    std::vector<double> fs;
    std::vector<yocto::vec<double, 3>> ws, zero;
    for (int i = 0; i < N; i++) {
      const double zc = 1 - (i + 0.5) * 2.0 / N, rr = std::sqrt(1 - zc * zc), ph = i * 2.399963229728653;
      const yocto::vec<double, 3> w{rr * std::cos(ph), rr * std::sin(ph), zc};
      const double f = rigidity::EvalF(cons, w);
      fmax = std::max(fmax, f);
      fs.push_back(f);
      ws.push_back(w);
    }
    for (size_t i = 0; i < ws.size(); i++) if (fs[i] < 0.02 * fmax) zero.push_back(ws[i]);
    const auto mg = rigidity::FirstOrderMargin(verts, min_u, false);
    printf("worst axis (%.4f %.4f %.4f)\n", mg.axis.x, mg.axis.y, mg.axis.z);
    // principal axes of the near-zero set (f < 2% of max; second moments)
    double M[3][3] = {};
    for (const auto &w : zero)
      for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) M[a][b] += w[a] * w[b] / zero.size();
    printf("cap candidate view u (%.6f %.6f %.6f): %zu of %d axes with f_u(w) < 2%% of max (max f_u %.3g);"
           " second moments of those axes:\n", min_u.x, min_u.y, min_u.z, zero.size(), N, fmax);
    for (int a = 0; a < 3; a++) printf("  %8.4f %8.4f %8.4f\n", M[a][0], M[a][1], M[a][2]);
    // The pinning symmetry (step 2 of the automatic-cap design in
    // SEPTOPERT-IMPROVEMENTS.md, to-do 10): the linear symmetries of the
    // vertex set (orthogonal maps permuting it, found from the images of
    // three independent vertices) that map the view to +-itself.
    using V3 = yocto::vec<double, 3>;
    const size_t nv = verts.size();
    size_t i0 = 0, i1 = 1, i2 = 2;
    for (i2 = 2; i2 < nv; i2++)
      if (std::abs(yocto::dot(yocto::cross(verts[i0], verts[i1]), verts[i2])) > 1e-3) break;
    CHECK(i2 < nv);
    const auto det3 = [](V3 a, V3 b, V3 c) { return yocto::dot(a, yocto::cross(b, c)); };
    int nsym = 0;
    for (size_t j0 = 0; j0 < nv; j0++)
      for (size_t j1 = 0; j1 < nv; j1++)
        for (size_t j2 = 0; j2 < nv; j2++) {
          // G with G v_i = v_j for the three chosen vertices: G = W V^-1.
          const V3 a = verts[i0], b = verts[i1], c = verts[i2];
          const double D = det3(a, b, c);
          // rows of V^-1 (V has columns a, b, c)
          const V3 r0 = yocto::cross(b, c) / D, r1 = yocto::cross(c, a) / D, r2 = yocto::cross(a, b) / D;
          const V3 A = verts[j0], B = verts[j1], C = verts[j2];
          auto G = [&](V3 x) { return A * yocto::dot(r0, x) + B * yocto::dot(r1, x) + C * yocto::dot(r2, x); };
          bool ok = true;
          for (size_t k = 0; k < nv && ok; k++) {
            const V3 y = G(verts[k]);
            bool hit = false;
            for (size_t l = 0; l < nv && !hit; l++) hit = yocto::length(y - verts[l]) < 1e-9;
            ok = hit;
          }
          if (!ok) continue;
          // orthogonal?
          const V3 e[3] = {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}};
          for (int p = 0; p < 3 && ok; p++)
            for (int q = 0; q < 3 && ok; q++)
              ok = std::abs(yocto::dot(G(e[p]), G(e[q])) - (p == q ? 1.0 : 0.0)) < 1e-9;
          if (!ok) continue;
          nsym++;
          const V3 gu = G(min_u);
          const double c1 = yocto::dot(gu, min_u);
          if (std::abs(std::abs(c1) - 1) > 1e-9) continue;
          const double tr = G(e[0]).x + G(e[1]).y + G(e[2]).z;
          const double dt = det3(G(e[0]), G(e[1]), G(e[2]));
          printf("  symmetry with g u = %+.0f u: det %+.0f, trace %+.3f%s\n", c1, dt, tr,
                 (dt < 0 && std::abs(tr - 1) < 1e-9) ? " (a mirror)" :
                 (dt > 0 && std::abs(tr + 1) < 1e-9) ? " (a half-turn)" : "");
        }
    printf("  (%d linear symmetries of the vertex set)\n", nsym);
  }
}
