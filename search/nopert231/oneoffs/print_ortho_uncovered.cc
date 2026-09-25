#include <iostream>
#include <vector>
#include <cmath>
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

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double box_delta = 234013.0 / 1000000000.0;
  double cos_max = c_cone / norm_u0;
  double R = std::sqrt(std::max(0.0, 1.0 - cos_max * cos_max));

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

  // Also search for any hull axes with c0 >= 0 regardless of FindAllHullSupportAxes limit
  std::cout << "Candidate axes: " << candidate_axes.size() << "\n";

  // Check N=4 grid
  int N = 4;
  for (int i = 0; i < N; i++) {
    double x_min = -R + 2.0 * R * i / N;
    double x_max = -R + 2.0 * R * (i + 1) / N;
    for (int j = 0; j < N; j++) {
      double y_min = -R + 2.0 * R * j / N;
      double y_max = -R + 2.0 * R * (j + 1) / N;

      double cx = std::max(0.0, std::max(x_min, -x_max));
      double cy = std::max(0.0, std::max(y_min, -y_max));
      if (cx * cx + cy * cy > R * R) continue;

      double best_corner = -1e9;
      int best_a = -1;
      for (size_t a = 0; a < candidate_axes.size(); a++) {
        const auto &ax = candidate_axes[a];
        double c1_corner = (ax.c1 >= 0) ? (ax.c1 * x_min) : (ax.c1 * x_max);
        double c2_corner = (ax.c2 >= 0) ? (ax.c2 * y_min) : (ax.c2 * y_max);
        double min_corner = c1_corner + c2_corner + ax.c0 * c_cone;
        if (min_corner > best_corner) {
          best_corner = min_corner;
          best_a = a;
        }
      }
      std::cout << "Cell (" << i << ", " << j << ") [" << x_min << ", " << x_max << "] x ["
                << y_min << ", " << y_max << "]: best_corner = " << best_corner
                << " (needed " << c_core << "), best_ax = " << (best_a >= 0 ? candidate_axes[best_a].id : -1) << "\n";
    }
  }

  return 0;
}
