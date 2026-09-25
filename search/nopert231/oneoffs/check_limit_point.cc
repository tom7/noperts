#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

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
  double norm_u0 = std::sqrt(yocto::dot(u0, u0));
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double x = 0.919;
  double y = 0.908;
  vec3 a = yocto::normalize(x * k1 + y * k2 + e3);

  std::cout << "a . u0 = " << yocto::dot(a, u0) << "\n";

  double box_delta = 165676.0 / 1000000000.0;
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

  std::cout << "Best dot at exact point a: " << best_dot
            << " (best axis idx " << best_idx
            << ", delta = " << axes[best_idx].delta.ToDouble() << ")\n";
  std::cout << "c_core = 0.0001657: margin = " << (best_dot - 0.0001657) << "\n";
  return 0;
}
