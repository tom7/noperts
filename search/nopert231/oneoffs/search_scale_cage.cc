#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Loaded " << axes.size() << " hull support axes.\n";

  std::vector<vec3> u;
  for (const auto &ax : axes) {
    u.push_back(vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                     ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                     ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  double B0 = ax0.B.ToDouble();
  double delta = del0.ToDouble();
  double D0 = 7.34e-5; // from tree_0.json

  std::cout << "B0 = " << B0 << ", delta = " << delta << ", D0 = " << D0 << "\n";

  // We want to find:
  // c_cone in [0.02, 0.40]
  // box_c in [delta + 0.0001, c_cone]
  // s = (box_c + delta) / c_cone
  // r in [r_min, 2 * (box_c - delta)]
  // r_min > D0 / ((c_cone - delta) * B0)
  // And (v0, u_i, u_j, u_k) cages octahedron of size 1.75 * (box_c + delta)

  int N = u.size();

  for (double c_cone : {0.028, 0.030, 0.032, 0.035, 0.038, 0.040, 0.045, 0.050}) {
    double min_r_min = D0 / ((c_cone - delta) * B0);

    for (double box_c : {0.001, 0.0015, 0.002, 0.0025, 0.003, 0.004}) {

      if (box_c <= delta) continue;
      double c_eff = box_c - delta;
      double max_r = 2.0 * c_eff / std::sqrt(1.0 + c_eff * c_eff);

      // Check if there is headroom for r: max_r > min_r_min
      if (max_r <= min_r_min * 1.2) continue;

      double scale = (box_c + delta) / c_cone;
      vec3 v0 = u0 * scale;

      double R = 1.75 * (box_c + delta);
      std::vector<vec3> oct = {
        {R, 0, 0}, {-R, 0, 0},
        {0, R, 0}, {0, -R, 0},
        {0, 0, R}, {0, 0, -R}
      };

      // Search for cage among u
      double best_min_l = -1;
      int best_i = -1, best_j = -1, best_k = -1;

      for (int i = 0; i < N; i++) {
        vec3 v1 = u[i];
        for (int j = i + 1; j < N; j++) {
          vec3 v2 = u[j];
          for (int k = j + 1; k < N; k++) {
            vec3 v3 = u[k];

            vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
            double det = yocto::dot(d1, yocto::cross(d2, d3));
            if (std::abs(det) < 1e-8) continue;
            vec3 c23 = yocto::cross(d2, d3);

            double min_l = 1e9;
            for (const auto &p : oct) {
              vec3 dp = p - v0;
              double l1 = yocto::dot(dp, c23) / det;
              double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
              double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
              double l0 = 1.0 - l1 - l2 - l3;
              min_l = std::min({min_l, l0, l1, l2, l3});
            }

            if (min_l > best_min_l) {
              best_min_l = min_l;
              best_i = i; best_j = j; best_k = k;
              if (best_min_l > 0.001) goto found_cage;
            }
          }
        }
      }

found_cage:
      if (best_min_l > 0) {
        std::cout << "FOUND SOLUTION: c_cone=" << c_cone << ", box_c=" << box_c
                  << ", scale=" << scale << ", min_l=" << best_min_l
                  << ", r range: [" << min_r_min << ", " << max_r << "]"
                  << ", cage: (" << best_i << ", " << best_j << ", " << best_k << ")\n";
        return 0;
      }
    }
  }

  std::cout << "No full solution found.\n";
  return 0;
}
