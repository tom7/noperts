// pool_check: compares the pool's weighted_defect_upper (Pareto frontiers)
// with the direct maximum over all vertices, on triangles around the DH caps.
#include <cmath>
#include <cstdio>
#include "base/logging.h"
#include "contacts5d.h"
#include "geom5d.h"
#include "model.h"
using vec3 = geom5d::vec3;
static double Direct(const geom5d::TriangleD &tri, const contacts5d::ContactPool &pool, const contacts5d::Triple &t) {
  auto coeffs = [&](const std::array<int, 3> &c) -> std::array<vec3, 3> {
    const vec3 &e0 = pool.contacts[c[0]].edge, &e1 = pool.contacts[c[1]].edge, &e2 = pool.contacts[c[2]].edge;
    return {yocto::cross(e1, e2), yocto::cross(e2, e0), yocto::cross(e0, e1)};
  };
  const auto w_coeff = coeffs(t.c);
  double total = 0;
  for (int i = 0; i < 3; i++) {
    const auto &ct = pool.contacts[t.c[i]];
    double w[3];
    for (int a = 0; a < 3; a++) w[a] = yocto::dot(tri.corners[a], w_coeff[i]) + 1e-9;
    double upper = 0;
    for (int k = 0; k < NUM_VERTICES; k++) {
      if (k == ct.vertex) continue;
      const vec3 s_coeff = yocto::cross(ct.edge, Vertex(k) - Vertex(ct.vertex));
      double s[3];
      for (int a = 0; a < 3; a++) s[a] = yocto::dot(tri.corners[a], s_coeff) + 1e-9;
      for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) upper = std::max(upper, 0.5 * (w[a] * s[b] + w[b] * s[a]));
    }
    total += upper;
  }
  return total;
}
int main() {
  const vec3 centers[2] = {{0.30901699437494740, 0.42532540417601999, 0.85065080835203999},
                           {0.42532540417601994, 0.13819660112501050, 0.89442719099991588}};
  int64_t n = 0, bad = 0;
  for (const vec3 &c0 : centers) {
    for (int s = 0; s < 6; s++) {
      const double d = 0.005 + 0.006 * s, ang = 1.1 * s;
      vec3 a = yocto::normalize(yocto::cross(c0, vec3{0, 0, 1})), b = yocto::cross(c0, a);
      vec3 c = yocto::normalize(c0 + d * (std::cos(ang) * a + std::sin(ang) * b));
      const double h = 0.004;
      geom5d::TriangleD tri;
      tri.corners[0] = c;
      tri.corners[1] = yocto::normalize(c + h * a);
      tri.corners[2] = yocto::normalize(c + h * b);
      const auto pool = contacts5d::BuildContactPool(tri, contacts5d::PoolParams{});
      for (const auto &t : pool.triples) {
        n++;
        const double dv = Direct(tri, pool, t);
        if (std::abs(dv - t.weighted_defect_upper) > 1e-14 * std::abs(dv)) { if (bad++ < 5) printf("mismatch %.17g %.17g\n", dv, t.weighted_defect_upper); }
      }
    }
  }
  printf("%lld triples, %lld mismatches\n", (long long)n, (long long)bad);
  return bad != 0;
}
