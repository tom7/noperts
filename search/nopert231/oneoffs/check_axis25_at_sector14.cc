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
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.017;
  double cos_cap = c_cone / norm_u0;
  double alpha_cap = std::acos(cos_cap);

  int N_ring = 16;
  double dphi = 2.0 * M_PI / N_ring;

  double B25 = axes[25].cert.B.ToDouble();
  vec3 v25 = vec3{axes[25].center.x.ToDouble() / B25, axes[25].center.y.ToDouble() / B25, axes[25].center.z.ToDouble() / B25};

  for (int i = 12; i <= 15; i++) {
    double phi1 = i * dphi;
    double phi2 = (i + 1) * dphi;
    vec3 p1 = yocto::normalize(std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi1) * k1 + std::sin(phi1) * k2));
    vec3 p2 = yocto::normalize(std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi2) * k1 + std::sin(phi2) * k2));

    std::cout << "Sector " << i << ":\n";
    std::cout << "  dot(u0, v25) = " << yocto::dot(u0, v25) << "\n";
    std::cout << "  dot(p1, v25) = " << yocto::dot(p1, v25) << "\n";
    std::cout << "  dot(p2, v25) = " << yocto::dot(p2, v25) << "\n";
  }

  return 0;
}
