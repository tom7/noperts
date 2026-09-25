#include <iostream>
#include <vector>
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

  // Sector 14 is phi in [14 * dphi, 15 * dphi]
  // Let's sample a grid in Sector 14:
  // r in [0, alpha_cap], phi in [14*dphi, 15*dphi]
  std::vector<vec3> cand_v;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000165) {
      double B = axes[i].cert.B.ToDouble();
      cand_v.push_back(vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B});
    }
  }

  double min_max_dot = 1e9;
  vec3 worst_pt;
  double worst_r = 0, worst_phi = 0;

  for (double r = 0; r <= alpha_cap; r += alpha_cap / 20.0) {
    for (double phi = 13.0 * dphi; phi <= 15.0 * dphi; phi += dphi / 20.0) {
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_dot = -1e9;
      for (const auto &v : cand_v) {
        max_dot = std::max(max_dot, yocto::dot(pt, v));
      }
      if (max_dot < min_max_dot) {
        min_max_dot = max_dot;
        worst_pt = pt;
        worst_r = r;
        worst_phi = phi;
      }
    }
  }

  std::cout << "Worst point in Sectors 13-14:\n";
  std::cout << "  r = " << worst_r << " (alpha_cap = " << alpha_cap << ")\n";
  std::cout << "  phi = " << worst_phi << " (" << worst_phi / dphi << " * dphi)\n";
  std::cout << "  min_max_dot = " << min_max_dot << "\n";
  std::cout << "  dot(worst_pt, u0) = " << yocto::dot(worst_pt, u0) << "\n";

  return 0;
}
