#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct CandidateAxis {
  vec3 v;
  double delta;
  int id;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);
  double norm_u0 = std::sqrt(norm_u0_sq);
  vec3 u0_hat = u0 / norm_u0;

  vec3 arbitrary = (std::abs(u0_hat.z) < 0.9) ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 k1 = yocto::normalize(yocto::cross(u0_hat, arbitrary));
  vec3 k2 = yocto::cross(u0_hat, k1);

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double box_delta = 234013.0 / 1000000000.0;

  std::vector<CandidateAxis> pool;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      vec3 v = vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                    ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                    ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
      pool.push_back({v, ax.delta.ToDouble(), (int)i});
    }
  }

  // Also add grid axes with {2,1,1,4}, {10,15,15,19}, {3,2,2,1}
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(0))) {
        if (del.ToDouble() <= box_delta) {
          vec3 v = vec3{ctr.x.ToDouble() / cert.B.ToDouble(),
                        ctr.y.ToDouble() / cert.B.ToDouble(),
                        ctr.z.ToDouble() / cert.B.ToDouble()};
          pool.push_back({v, del.ToDouble(), 10000 + m1 * 100 + m2});
        }
      }
    }
  }

  vec3 P0 = u0 / norm_u0_sq;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);

  int N = 16;
  double step = (2.0 * R) / N;
  for (int i = 0; i < N; i++) {
    double x_min = -R + i * step;
    double x_max = x_min + step;
    for (int j = 0; j < N; j++) {
      double y_min = -R + j * step;
      double y_max = y_min + step;

      double closest_x = std::max(0.0, std::max(x_min, -x_max));
      double closest_y = std::max(0.0, std::max(y_min, -y_max));
      if (closest_x * closest_x + closest_y * closest_y > R * R) continue;

      double xs[4] = {x_min, x_max, x_min, x_max};
      double ys[4] = {y_min, y_min, y_max, y_max};

      bool box_covered = false;
      double best_min_corner = -1.0;
      for (const auto &ax : pool) {
        double min_corner = 1e9;
        for (int c = 0; c < 4; c++) {
          vec3 p = P0 + xs[c] * k1 + ys[c] * k2;
          vec3 a = yocto::normalize(p);
          double d = yocto::dot(a, ax.v);
          if (d < min_corner) min_corner = d;
        }
        if (min_corner > best_min_corner) best_min_corner = min_corner;
        if (min_corner >= c_core) {
          box_covered = true;
          break;
        }
      }
      if (!box_covered) {
        std::cout << "Uncovered box: [" << x_min << ", " << x_max << "] x ["
                  << y_min << ", " << y_max << "], best min corner = "
                  << best_min_corner << " (target " << c_core << ", deficit "
                  << c_core - best_min_corner << ")\n";
      }
    }
  }

  return 0;
}
