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
  double dphi = 2.0 * M_PI / 16.0;

  std::vector<std::pair<int, vec3>> good_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000165) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      good_axes.push_back({(int)i, v});
    }
  }

  double min_cover = 1e9;
  double worst_r = 0, worst_phi = 0;
  for (double r = 0; r <= alpha_cap; r += alpha_cap / 40.0) {
    for (double phi = 13.4 * dphi; phi <= 14.6 * dphi; phi += dphi / 40.0) {
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_d = -1e9;
      for (const auto &ga : good_axes) {
        max_d = std::max(max_d, yocto::dot(pt, ga.second));
      }
      if (max_d < min_cover) {
        min_cover = max_d;
        worst_r = r;
        worst_phi = phi;
      }
    }
  }

  std::cout << "worst_r = " << worst_r << " (ratio = " << worst_r / alpha_cap << ")\n";
  std::cout << "worst_phi = " << worst_phi << " (phi/dphi = " << worst_phi / dphi << ")\n";
  std::cout << "min_cover = " << min_cover << "\n";
  return 0;
}
