#include <iostream>
#include <vector>
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

  // Candidate axes:
  // Must have:
  // 1. delta <= 0.000165
  // 2. dot(u0, v) >= c_core
  double c_core = 0.0005;

  std::vector<std::pair<int, vec3>> valid_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() > 0.000165) continue;
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    if (yocto::dot(u0, v) < c_core) continue;
    valid_axes.push_back({(int)i, v});
  }

  std::cout << "Valid axes with dot(u0, v) >= " << c_core << ": " << valid_axes.size() << "\n";

  // Now for each of the 16 sectors, check which axes cover the sector vertices u0, p1, p2!
  for (int s = 0; s < N_ring; s++) {
    double phi1 = s * dphi;
    double phi2 = (s + 1) * dphi;
    vec3 p1 = yocto::normalize(std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi1) * k1 + std::sin(phi1) * k2));
    vec3 p2 = yocto::normalize(std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi2) * k1 + std::sin(phi2) * k2));

    std::vector<int> covering;
    for (const auto &va : valid_axes) {
      if (yocto::dot(u0, va.second) >= c_core &&
          yocto::dot(p1, va.second) >= c_core &&
          yocto::dot(p2, va.second) >= c_core) {
        covering.push_back(va.first);
      }
    }
    std::cout << "Sector " << s << ": covered by " << covering.size() << " axes";
    if (!covering.empty()) {
      std::cout << " (e.g. Axis " << covering[0] << ")";
    }
    std::cout << "\n";
  }

  return 0;
}
