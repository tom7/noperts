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

  int N = u.size();

  double box_c = 0.003;
  double delta = 0.000234;
  double c_cone = 0.015;
  double K = box_c + delta;
  vec3 v0 = u0 * (K / c_cone);
  double R = 1.75 * K;
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::cout << "v0 = (" << v0.x << ", " << v0.y << ", " << v0.z << "), |v0| = " << yocto::length(v0) << ", R = " << R << "\n";

  double best_min_l = -1;
  int b1 = -1, b2 = -1, b3 = -1;

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
          b1 = i; b2 = j; b3 = k;
          if (best_min_l > 0.001) goto done_search;
        }
      }
    }
  }

done_search:
  std::cout << "best_min_l = " << best_min_l << " with cage (" << b1 << ", " << b2 << ", " << b3 << ")\n";
  return 0;


  return 0;
}
