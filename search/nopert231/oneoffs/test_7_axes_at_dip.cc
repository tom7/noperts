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
  double norm_u0 = std::sqrt(norm_u0_sq);
  vec3 u0_hat = u0 / norm_u0;

  vec3 arbitrary = (std::abs(u0_hat.z) < 0.9) ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 k1 = yocto::normalize(yocto::cross(u0_hat, arbitrary));
  vec3 k2 = yocto::cross(u0_hat, k1);

  vec3 P0 = u0 / norm_u0_sq;
  double x = 24.5, y = -19.0791;
  vec3 p = P0 + x * k1 + y * k2;
  vec3 a = yocto::normalize(p);

  std::cout << "Target direction a: (" << a.x << ", " << a.y << ", " << a.z << ")\n";
  std::cout << "Inner product with u0: " << yocto::dot(a, u0) << "\n";

  int test_indices[] = {25, 175, 221, 1772, 2180, 2941, 2951};
  for (int idx : test_indices) {
    const auto &ax = axes[idx];
    vec3 v = vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                  ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                  ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    double d = yocto::dot(a, v);
    std::cout << "Axis " << idx << " (delta " << ax.delta.ToDouble() << "): dot = " << d << "\n";
  }

  return 0;
}
