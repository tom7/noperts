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

  // Annular axis ax0:
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

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  std::cout << "norm(u0) = " << norm_u0 << ", cos(alpha) = " << cos_alpha
            << ", alpha = " << (alpha * 180.0 / M_PI) << " deg\n";

  std::vector<int> flock_indices = {25, 175, 221, 1772, 2180, 2941, 2951};
  std::vector<vec3> flock_v;
  for (int idx : flock_indices) {
    double B = axes[idx].cert.B.ToDouble();
    vec3 v = vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B};
    flock_v.push_back(v);
    std::cout << "Axis " << idx << ": norm = " << yocto::length(v)
              << ", delta = " << axes[idx].delta.ToDouble()
              << ", dot(u0, v) = " << yocto::dot(u0, v) << "\n";
  }

  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double min_val = 1e9;
  for (double r = 0; r <= alpha; r += alpha / 400.0) {
    int num_phi = std::max(1, (int)std::ceil(800.0 * (r / alpha)));
    for (int p = 0; p < num_phi; p++) {
      double phi = 2.0 * M_PI * p / num_phi;
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_m = -1e9;
      for (const auto &v : flock_v) max_m = std::max(max_m, yocto::dot(pt, v));
      min_val = std::min(min_val, max_m);
    }
  }
  std::cout << "Continuous grid minimum coverage with the 7 flock axes: " << min_val << "\n";

  return 0;
}
