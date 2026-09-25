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
  double norm_u0 = yocto::length(u0);
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double x = 0.534, y = 0.638;
  double z = std::sqrt(std::max(0.0, 1.0 - x*x - y*y));
  vec3 a = x * k1 + y * k2 + z * e3;

  std::cout << "Adv dot(a, u0) = " << yocto::dot(a, u0) << "\n";

  std::vector<std::pair<double, int>> best_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    double B = ax.cert.B.ToDouble();
    vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
    double d = yocto::dot(a, v);
    best_axes.push_back({d, (int)i});
  }
  std::sort(best_axes.rbegin(), best_axes.rend());

  std::cout << "Top axes for this adversary:\n";
  for (int k = 0; k < 10; k++) {
    int idx = best_axes[k].second;
    std::cout << "  #" << k << ": idx " << idx << ": dot = " << best_axes[k].first
              << ", delta = " << axes[idx].delta.ToDouble() << "\n";
  }

  return 0;
}
