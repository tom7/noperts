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

  std::cout << "Candidate pool size: " << pool.size() << "\n";

  // Test grid sizes N = 2, 3, 4, 5, 6, 8, 10
  vec3 P0 = u0 / norm_u0_sq;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);
  std::cout << "Cone radius R = " << R << "\n";

  for (int N : {2, 4, 6, 8, 10, 12, 16}) {
    double step = (2.0 * R) / N;
    int uncovered = 0;
    std::set<int> used_axes;
    for (int i = 0; i < N; i++) {
      double x_min = -R + i * step;
      double x_max = x_min + step;
      for (int j = 0; j < N; j++) {
        double y_min = -R + j * step;
        double y_max = y_min + step;

        // Check if box intersects the disk x^2 + y^2 <= R^2:
        double closest_x = std::max(0.0, std::max(x_min, -x_max));
        double closest_y = std::max(0.0, std::max(y_min, -y_max));
        if (closest_x * closest_x + closest_y * closest_y > R * R) {
          continue; // Outside cone
        }

        // 4 corners:
        double xs[4] = {x_min, x_max, x_min, x_max};
        double ys[4] = {y_min, y_min, y_max, y_max};

        bool box_covered = false;
        for (const auto &ax : pool) {
          bool all_corners = true;
          for (int c = 0; c < 4; c++) {
            vec3 p = P0 + xs[c] * k1 + ys[c] * k2;
            vec3 a = yocto::normalize(p);
            if (yocto::dot(a, ax.v) < c_core) {
              all_corners = false;
              break;
            }
          }
          if (all_corners) {
            box_covered = true;
            used_axes.insert(ax.id);
            break;
          }
        }
        if (!box_covered) uncovered++;
      }
    }
    std::cout << "Grid " << N << "x" << N << ": uncovered boxes = " << uncovered
              << ", used distinct axes = " << used_axes.size() << "\n";
  }

  return 0;
}
