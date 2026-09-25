#include <iostream>
#include <iomanip>
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
  double norm_u0 = yocto::length(u0);
  vec3 u0_hat = u0 / norm_u0;

  // Orthonormal basis k1, k2 for u0_perp
  vec3 arbitrary = (std::abs(u0_hat.z) < 0.9) ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 k1 = yocto::normalize(yocto::cross(u0_hat, arbitrary));
  vec3 k2 = yocto::cross(u0_hat, k1);

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), norm=" << norm_u0 << "\n";
  std::cout << "k1: (" << k1.x << ", " << k1.y << ", " << k1.z << ")\n";
  std::cout << "k2: (" << k2.x << ", " << k2.y << ", " << k2.z << ")\n";

  // Check the 4 flock axes from Section 6:
  // Axis 3054, Axis 31, Axis 3059, Axis 3058
  // Or check all valid axes:
  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) {
      valid_axes.push_back(ax);
    }
  }

  double c_cone = 0.015;
  double c_core = 0.003; // or what can we achieve?

  std::cout << "Testing boxes over [-1, 1]^2 for c_cone=" << c_cone << "...\n";
  return 0;
}
