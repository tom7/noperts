#include <iostream>
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

  vec3 a = yocto::normalize(vec3{0.3992, -0.4799, -0.7813});
  std::cout << "a . u0 = " << yocto::dot(a, u0) << "\n";

  // Check the cage axes!
  const auto &ax1 = axes[23];
  const auto &ax2 = axes[24];
  const auto &ax3 = axes[210];

  double B1 = ax1.cert.B.ToDouble();
  double B2 = ax2.cert.B.ToDouble();
  double B3 = ax3.cert.B.ToDouble();
  vec3 v1 = vec3{ax1.center.x.ToDouble() / B1, ax1.center.y.ToDouble() / B1, ax1.center.z.ToDouble() / B1};
  vec3 v2 = vec3{ax2.center.x.ToDouble() / B2, ax2.center.y.ToDouble() / B2, ax2.center.z.ToDouble() / B2};
  vec3 v3 = vec3{ax3.center.x.ToDouble() / B3, ax3.center.y.ToDouble() / B3, ax3.center.z.ToDouble() / B3};

  std::cout << "a . v1 = " << yocto::dot(a, v1) << ", delta1 = " << ax1.delta.ToDouble() << "\n";
  std::cout << "a . v2 = " << yocto::dot(a, v2) << ", delta2 = " << ax2.delta.ToDouble() << "\n";
  std::cout << "a . v3 = " << yocto::dot(a, v3) << ", delta3 = " << ax3.delta.ToDouble() << "\n";

  return 0;
}
