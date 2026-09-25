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

  // Let's collect all axes from axes that have delta <= 0.000165:
  std::vector<std::pair<int, vec3>> good_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000165) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      good_axes.push_back({(int)i, v});
    }
  }

  // Also include the cage axes (ax1, ax2):
  // Let's see: Axis 23 and 24 are in axes anyway.
  std::cout << "Good axes count: " << good_axes.size() << "\n";

  // Check the gap: phi in [13.5 * dphi, 14.5 * dphi], r in [0, alpha_cap]
  double min_cover = 1e9;
  vec3 worst_p;
  for (double r = 0; r <= alpha_cap; r += alpha_cap / 40.0) {
    for (double phi = 13.4 * dphi; phi <= 14.6 * dphi; phi += dphi / 40.0) {
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_d = -1e9;
      int best_id = -1;
      for (const auto &ga : good_axes) {
        double d = yocto::dot(pt, ga.second);
        if (d > max_d) {
          max_d = d;
          best_id = ga.first;
        }
      }
      if (max_d < min_cover) {
        min_cover = max_d;
        worst_p = pt;
      }
    }
  }

  std::cout << "In gap (phi 13.4 to 14.6): min_cover across all good hull axes = " << min_cover << "\n";
  if (min_cover < 0) {
    std::cout << "Negative margin! Finding top axes at worst_p:\n";
    std::vector<std::pair<double, int>> dots;
    for (const auto &ga : good_axes) {
      dots.push_back({yocto::dot(worst_p, ga.second), ga.first});
    }
    std::sort(dots.rbegin(), dots.rend());
    for (int i = 0; i < 5; i++) {
      std::cout << "  Axis " << dots[i].second << ": dot = " << dots[i].first << "\n";
    }
  }

  return 0;
}
