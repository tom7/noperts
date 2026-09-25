#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

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
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()}) / ax0.B.ToDouble();
  double cos_alpha = c_cone / norm_u0;

  int flock_idx[5] = {3064, 174, 3054, 4911, 4924};
  vec3 v[5];
  for (int m = 0; m < 5; m++) {
    int idx = flock_idx[m];
    ContactInfo cts[3] = {axes[idx].cert.contacts[0], axes[idx].cert.contacts[1], axes[idx].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v[m] = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
  }

  double global_min_max = 1e9;
  vec3 worst_a = {0, 0, 0};

  // Dense search on cap
  for (double z = cos_alpha; z <= 1.0; z += 0.001) {
    double r_xy = std::sqrt(std::max(0.0, 1.0 - z * z));
    int N_phi = std::max(10, (int)(r_xy * 2000));
    for (int p = 0; p < N_phi; p++) {
      double phi = 2.0 * M_PI * p / N_phi;
      vec3 a = z * u0 + r_xy * (std::cos(phi) * k1 + std::sin(phi) * k2);
      double max_dot = -1e9;
      for (int m = 0; m < 5; m++) {
        double d = yocto::dot(a, v[m]);
        if (d > max_dot) max_dot = d;
      }
      if (max_dot < global_min_max) {
        global_min_max = max_dot;
        worst_a = a;
      }
    }
  }

  std::cout << "Across 1,000,000 points on cap: global_min_max = " << global_min_max << "\n";
  std::cout << "Worst a: dot(a, u0) = " << yocto::dot(worst_a, u0)
            << ", dot(a, k1) = " << yocto::dot(worst_a, k1)
            << ", dot(a, k2) = " << yocto::dot(worst_a, k2) << "\n";
  for (int m = 0; m < 5; m++) {
    std::cout << "  dot(worst_a, v[" << m << "]) = " << yocto::dot(worst_a, v[m]) << "\n";
  }

  return 0;
}
