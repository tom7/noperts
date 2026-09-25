#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

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

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Loaded " << base_axes.size() << " hull support axes.\n";

  std::vector<vec3> u;
  for (const auto &ax : base_axes) {
    u.push_back({ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                 ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                 ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  double delta = 0.000234013;
  for (double c_cone : {0.028, 0.029, 0.030, 0.032, 0.035}) {

    for (double box_c : {0.0005, 0.0008, 0.001, 0.0012, 0.0015, 0.002, 0.003}) {
      double scale = (box_c + delta) / c_cone;
      vec3 v0 = u0 * scale;
      double R = 1.75 * (box_c + delta);

    std::vector<vec3> oct = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };

    double best_min_l = -1;
    int best_i = -1, best_j = -1, best_k = -1;

    int N = u.size();
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
          }
        }
      }
    }

    std::cout << "c_cone = " << c_cone << ", box_c = " << box_c << " (scale = " << scale << ", R = " << R << "): "
              << "best_min_l = " << best_min_l << " with axes (" << best_i << ", " << best_j << ", " << best_k << ")\n";
    }
  }

  return 0;
}
