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

  int idx = 3183;
  const auto &ax = axes[idx];
  double B = ax.cert.B.ToDouble();
  vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
  double c1 = yocto::dot(v, k1);
  double c2 = yocto::dot(v, k2);
  double c0 = yocto::dot(v, u0) / (norm_u0 * norm_u0);

  double x_min = 0.294998, x_max = 0.296865;
  double y_min = 0.300599, y_max = 0.302466;
  double c_cone = 0.015;

  double c1_c = (c1 >= 0) ? (c1 * x_min) : (c1 * x_max);
  double c2_c = (c2 >= 0) ? (c2 * y_min) : (c2 * y_max);
  double val = c1_c + c2_c + c0 * c_cone;

  std::cout << "Axis 3183: c0 = " << c0 << ", c1 = " << c1 << ", c2 = " << c2 << "\n";
  std::cout << "c1_c = " << c1_c << ", c2_c = " << c2_c << ", c0 * c_cone = " << c0 * c_cone << "\n";
  std::cout << "val = " << val << "\n";

  return 0;
}
