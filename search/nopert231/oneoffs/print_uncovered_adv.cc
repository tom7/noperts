#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

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

  // Let's examine the center of Cell (2, 2) in the 4x4 grid:
  // x in [0, 0.477972], y in [0, 0.477972]
  // Let x = 0.24, y = 0.24
  double x = 0.24, y = 0.24;
  double z = std::sqrt(std::max(0.0, 1.0 - x*x - y*y));
  // Vector a:
  vec3 a = x * k1 + y * k2 + z * e3;
  std::cout << "Test adversary a = (" << a.x << ", " << a.y << ", " << a.z << "), norm = " << yocto::length(a) << "\n";
  std::cout << "dot(a, u0) = " << yocto::dot(a, u0) << " (needed >= " << c_cone << ")\n";

  // Now, what is the best axis in axes for this a?
  double best_dot = -1e9;
  int best_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double d = yocto::dot(a, v);
      if (d > best_dot) {
        best_dot = d;
        best_idx = i;
      }
    }
  }
  std::cout << "Best dot among all 5000 hull axes: " << best_dot << " (idx " << best_idx << ")\n";

  // What about any axis in the entire library without delta constraint?
  double all_best_dot = -1e9;
  int all_best_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    double B = ax.cert.B.ToDouble();
    vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
    double d = yocto::dot(a, v);
    if (d > all_best_dot) {
      all_best_dot = d;
      all_best_idx = i;
    }
  }
  std::cout << "Best dot among ALL axes (no delta limit): " << all_best_dot << " (idx " << all_best_idx
            << ", delta = " << axes[all_best_idx].delta.ToDouble() << ")\n";

  return 0;
}
