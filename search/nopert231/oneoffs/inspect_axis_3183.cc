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

  vec3 E1 = vec3{1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = vec3{0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double c_cone = 0.015;
  double c_core = 0.000234060;

  const auto &ax = axes[3183];
  double B = ax.cert.B.ToDouble();
  vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
  double d0 = yocto::dot(P0, v);
  double d1 = yocto::dot(E1, v);
  double d2 = yocto::dot(E2, v);

  std::cout << "Axis 3183: d0 = " << d0 << ", d1 = " << d1 << ", d2 = " << d2 << "\n";

  // Box [0, 7.966] x [-7.966, 0]
  double x_min = 0, x_max = 7.966;
  double y_min = -7.966, y_max = 0;

  double c1_corner = (d1 >= 0) ? (d1 * x_min) : (d1 * x_max);
  double c2_corner = (d2 >= 0) ? (d2 * y_min) : (d2 * y_max);
  double min_corner = c1_corner + c2_corner + d0 * c_cone;
  std::cout << "min_corner on [0, 7.966] x [-7.966, 0] = " << min_corner << "\n";

  // What about smaller box: [0, 2] x [-2, 0]?
  x_min = 0; x_max = 2.0;
  y_min = -2.0; y_max = 0;
  c1_corner = (d1 >= 0) ? (d1 * x_min) : (d1 * x_max);
  c2_corner = (d2 >= 0) ? (d2 * y_min) : (d2 * y_max);
  std::cout << "min_corner on [0, 2] x [-2, 0] = " << c1_corner + c2_corner + d0 * c_cone << "\n";

  return 0;
}
