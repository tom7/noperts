#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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

  std::cout << "norm_u0 = " << norm_u0 << "\n";

  // Filter zero-defect axes:
  std::vector<std::pair<int, vec3>> cand_v;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000260) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      cand_v.push_back({(int)i, v});
    }
  }
  std::cout << "Cand axes with delta <= 0.000260: " << cand_v.size() << "\n";

  // Let us test different cone sizes c_cone:
  for (double c_cone : {0.025, 0.020, 0.015, 0.010, 0.005}) {
    double cos_alpha = c_cone / norm_u0;
    if (cos_alpha > 1.0) continue;
    double alpha = std::acos(cos_alpha);
    double alpha_deg = alpha * 180.0 / M_PI;

    vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
    vec3 k2 = yocto::cross(u0, k1);

    // Generate 10,000 cap points
    std::vector<vec3> cap_pts;
    for (int i = 0; i < 10000; i++) {
      double t = (double)i / 9999.0;
      double r = alpha * std::sqrt(t);
      double phi = i * 2.399963229728653;
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      cap_pts.push_back(pt);
    }

    // What is the upper bound on min_pt max_v (pt . v) if we used ALL cand_v?
    double all_min_dot = 1e9;
    for (const auto &pt : cap_pts) {
      double max_d = -1e9;
      for (const auto &cv : cand_v) {
        max_d = std::max(max_d, (double)yocto::dot(pt, cv.second));
      }
      all_min_dot = std::min(all_min_dot, max_d);
    }

    std::cout << "c_cone = " << c_cone << " (alpha = " << alpha_deg << " deg): max achievable c_core = " << all_min_dot << "\n";
  }

  return 0;
}
