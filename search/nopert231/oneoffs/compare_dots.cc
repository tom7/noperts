#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0_raw = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  vec3 u0 = yocto::normalize(u0_raw);

  // In inspect_sector14.cc:
  // centroid was printed as: (0.3992, -0.494824, -0.771874)
  vec3 c1 = {0.3992, -0.494824, -0.771874};
  std::cout << "c1 . u0_raw = " << yocto::dot(c1, u0_raw) << "\n";
  std::cout << "c1 normalized . u0_raw = " << yocto::dot(yocto::normalize(c1), u0_raw) << "\n";

  // Now let us compute the actual sector 14 from u0:
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);
  double alpha_cap = std::acos(0.017 / yocto::length(u0_raw));
  int N_ring = 16;
  double dphi = 2.0 * M_PI / N_ring;
  double phi1 = 14 * dphi;
  vec3 p_ring14 = std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi1) * k1 + std::sin(phi1) * k2);
  p_ring14 = yocto::normalize(p_ring14);
  std::cout << "p_ring14 = (" << p_ring14.x << ", " << p_ring14.y << ", " << p_ring14.z << ")\n";
  std::cout << "p_ring14 . u0_raw = " << yocto::dot(p_ring14, u0_raw) << "\n";

  return 0;
}
