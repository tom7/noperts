#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct AxisData {
  vec3 v;
  double c0, c1, c2;
  int id;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);
  double norm_u0 = std::sqrt(norm_u0_sq);
  vec3 e3 = u0 / norm_u0;

  // Build orthonormal basis k1, k2 perpendicular to u0
  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  std::cout << "e3 = (" << e3.x << ", " << e3.y << ", " << e3.z << ")\n";
  std::cout << "k1 = (" << k1.x << ", " << k1.y << ", " << k1.z << "), norm = " << yocto::length(k1) << "\n";
  std::cout << "k2 = (" << k2.x << ", " << k2.y << ", " << k2.z << "), norm = " << yocto::length(k2) << "\n";
  std::cout << "dot(k1, e3) = " << yocto::dot(k1, e3) << ", dot(k2, e3) = " << yocto::dot(k2, e3)
            << ", dot(k1, k2) = " << yocto::dot(k1, k2) << "\n";

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double box_delta = 234013.0 / 1000000000.0;

  double cos_max = c_cone / norm_u0;
  double R = std::sqrt(std::max(0.0, 1.0 - cos_max * cos_max));
  std::cout << "c_cone = " << c_cone << ", norm_u0 = " << norm_u0 << ", cos_max = " << cos_max << ", R = " << R << "\n";

  std::vector<AxisData> candidate_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double c1 = yocto::dot(v, k1);
      double c2 = yocto::dot(v, k2);
      double c0 = yocto::dot(v, u0) / norm_u0_sq;
      if (c0 >= 0) {
        candidate_axes.push_back({v, c0, c1, c2, (int)i});
      }
    }
  }

  // Add grid mixes
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate ax_cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &ax_cert, &center, &delta, &err, BigRat(0))) {
        if (delta.ToDouble() <= box_delta) {
          double B = ax_cert.B.ToDouble();
          vec3 v = vec3{center.x.ToDouble() / B, center.y.ToDouble() / B, center.z.ToDouble() / B};
          double c1 = yocto::dot(v, k1);
          double c2 = yocto::dot(v, k2);
          double c0 = yocto::dot(v, u0) / norm_u0_sq;
          if (c0 >= 0) {
            candidate_axes.push_back({v, c0, c1, c2, -1});
          }
        }
      }
    }
  }

  std::cout << "Candidate axes with c0 >= 0: " << candidate_axes.size() << "\n";

  for (int N : {4, 6, 8, 10, 12, 16, 20}) {
    int uncovered = 0;
    std::set<int> used_axes;
    for (int i = 0; i < N; i++) {
      double x_min = -R + 2.0 * R * i / N;
      double x_max = -R + 2.0 * R * (i + 1) / N;
      for (int j = 0; j < N; j++) {
        double y_min = -R + 2.0 * R * j / N;
        double y_max = -R + 2.0 * R * (j + 1) / N;

        double cx = std::max(0.0, std::max(x_min, -x_max));
        double cy = std::max(0.0, std::max(y_min, -y_max));
        if (cx * cx + cy * cy > R * R) continue;

        bool box_covered = false;
        for (size_t a = 0; a < candidate_axes.size(); a++) {
          const auto &ax = candidate_axes[a];
          double c1_corner = (ax.c1 >= 0) ? (ax.c1 * x_min) : (ax.c1 * x_max);
          double c2_corner = (ax.c2 >= 0) ? (ax.c2 * y_min) : (ax.c2 * y_max);
          double min_corner = c1_corner + c2_corner + ax.c0 * c_cone;
          if (min_corner >= c_core) {
            box_covered = true;
            used_axes.insert(a);
            break;
          }
        }
        if (!box_covered) {
          uncovered++;
        }
      }
    }
    std::cout << "Grid " << N << "x" << N << ": uncovered = " << uncovered
              << ", used axes = " << used_axes.size() << "\n";
    if (uncovered == 0) {
      std::cout << "SUCCESS! 100% COVERED at N = " << N << "!\n";
      break;
    }
  }

  return 0;
}
