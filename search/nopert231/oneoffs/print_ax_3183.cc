#include <iostream>
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

  std::cout << "Axis 3183: delta = " << ax.delta.ToDouble() << "\n";
  std::cout << "v = (" << v.x << ", " << v.y << ", " << v.z << ")\n";
  std::cout << "c0 = " << c0 << ", c1 = " << c1 << ", c2 = " << c2 << "\n";
  std::cout << "dot(v, e3) = " << yocto::dot(v, e3) << "\n";

  // If a is in [0, 0.48] x [0, 0.48]:
  // then x in [0, 0.48], y in [0, 0.48]
  // Since x^2 + y^2 <= 2 * 0.48^2 = 0.46,
  // z = a . e3 >= sqrt(1 - 0.46) = 0.734
  // So a . u0 = z * norm_u0 >= 0.734 * norm_u0 = 0.0375!
  double z_min = std::sqrt(1.0 - 0.478*0.478 - 0.478*0.478);
  double a_u0_min = z_min * norm_u0;
  double c1_corner = (c1 >= 0) ? (c1 * 0.0) : (c1 * 0.478);
  double c2_corner = (c2 >= 0) ? (c2 * 0.0) : (c2 * 0.478);
  double true_min_corner = c1_corner + c2_corner + c0 * a_u0_min;
  std::cout << "z_min = " << z_min << ", a_u0_min = " << a_u0_min << "\n";
  std::cout << "true_min_corner = " << true_min_corner << "\n";

  return 0;
}
