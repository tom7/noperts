#include <iostream>
#include <vector>
#include <algorithm>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int N = base_axes.size();

  std::vector<vec3> u(N);
  for (int i = 0; i < N; i++) {
    u[i] = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
            base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
            base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
  }

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.00026;
  double c_cone = 0.029;
  double R = 1.75 * (box_c + delta);
  vec3 v0 = u0 * ((box_c + delta) / c_cone);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::vector<int> fixed_cand = {421, 210, 212, 213, 389, 2949, 2933, 1689};
  double best_min_l = -1e9;
  int best_1 = -1, best_2 = -1, best_3 = -1;

  for (int idx1 : fixed_cand) {
    vec3 v1 = u[idx1];
    vec3 d1 = v1 - v0;
    std::cout << "Testing idx1 = " << idx1 << "...\n";
    for (int idx2 = 0; idx2 < N; idx2++) {
      if (idx2 == idx1) continue;
      vec3 v2 = u[idx2];
      vec3 d2 = v2 - v0;
      vec3 c12 = yocto::cross(d1, d2);
      for (int idx3 = idx2 + 1; idx3 < N; idx3++) {
        if (idx3 == idx1) continue;
        vec3 v3 = u[idx3];
        vec3 d3 = v3 - v0;
        double det = yocto::dot(c12, d3);
        if (std::abs(det) < 1e-9) continue;

        vec3 c23 = yocto::cross(d2, d3);
        vec3 c31 = yocto::cross(d3, d1);

        double min_l = 1.0;
        for (int p = 0; p < 6; p++) {
          vec3 dp = oct[p] - v0;
          double l1 = yocto::dot(dp, c23) / det;
          if (l1 < 0) { min_l = std::min(min_l, l1); if (min_l < best_min_l) goto next_p; }
          double l2 = yocto::dot(dp, c31) / det;
          if (l2 < 0) { min_l = std::min(min_l, l2); if (min_l < best_min_l) goto next_p; }
          double l3 = yocto::dot(dp, c12) / det;
          if (l3 < 0) { min_l = std::min(min_l, l3); if (min_l < best_min_l) goto next_p; }
          double l0 = 1.0 - l1 - l2 - l3;
          if (l0 < 0) { min_l = std::min(min_l, l0); if (min_l < best_min_l) goto next_p; }
          min_l = std::min({min_l, l0, l1, l2, l3});
        }
        if (min_l > best_min_l) {
          best_min_l = min_l;
          best_1 = idx1; best_2 = idx2; best_3 = idx3;
          std::cout << "New best_min_l = " << best_min_l << " with ("
                    << idx1 << ", " << idx2 << ", " << idx3 << ")\n";
          if (best_min_l > 0) {
            std::cout << "SUCCESS! Found enclosing cage!\n";
            return 0;
          }
        }
      next_p:;
      }
    }
  }

  std::cout << "Best min_l = " << best_min_l << " with ("
            << best_1 << ", " << best_2 << ", " << best_3 << ")\n";
  return 0;
}
