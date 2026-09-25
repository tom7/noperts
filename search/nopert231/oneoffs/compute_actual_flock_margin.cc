#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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

  int idx[] = {0, 1, 4};
  vec3 flock_v[3];
  for (int m = 0; m < 3; m++) {
    int i = idx[m];
    double B = axes[i].cert.B.ToDouble();
    flock_v[m] = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
  }

  double c_cone = 0.017;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  std::cout << "norm_u0: " << norm_u0 << ", cos_alpha: " << cos_alpha << ", alpha_deg: " << alpha * 180.0 / M_PI << "\n";

  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double min_cover_val = 1e9;
  for (double r = 0; r <= alpha; r += alpha / 100.0) {
    int num_phi = std::max(1, (int)std::ceil(400.0 * (r / alpha)));
    for (int p = 0; p < num_phi; p++) {
      double phi = 2.0 * M_PI * p / num_phi;
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_m = std::max({yocto::dot(pt, flock_v[0]), yocto::dot(pt, flock_v[1]), yocto::dot(pt, flock_v[2])});
      min_cover_val = std::min(min_cover_val, max_m);
    }
  }

  std::cout << "MINIMUM COVERAGE VALUE ACROSS CAP: " << min_cover_val << "\n";
  return 0;
}
