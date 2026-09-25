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

  double x1 = 0.375, x2 = 0.40625;
  double y1 = -0.5, y2 = -0.46875;
  double z1 = -0.8125, z2 = -0.78125;

  std::string err;
  double best_bound = -1e9;
  int best_idx = -1;
  vec3 best_v;

  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      double min_dot_v = (v.x >= 0 ? v.x * x1 : v.x * x2) +
                         (v.y >= 0 ? v.y * y1 : v.y * y2) +
                         (v.z >= 0 ? v.z * z1 : v.z * z2);
      if (min_dot_v > best_bound) {
        best_bound = min_dot_v;
        best_idx = i;
        best_v = v;
      }
    }
  }

  std::cout << "Best bound on box = " << best_bound << " (Axis " << best_idx << ")\n";
  std::cout << "Best v = (" << best_v.x << ", " << best_v.y << ", " << best_v.z << ")\n";

  // Center of box:
  vec3 mid = {(x1+x2)/2, (y1+y2)/2, (z1+z2)/2};
  vec3 mid_norm = yocto::normalize(mid);
  std::cout << "Mid norm = (" << mid_norm.x << ", " << mid_norm.y << ", " << mid_norm.z << ")\n";
  std::cout << "dot(mid_norm, best_v) = " << yocto::dot(mid_norm, best_v) << "\n";

  // Find axis with highest dot with mid_norm
  double max_dot_mid = -1e9;
  int best_mid_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      double d = yocto::dot(mid_norm, v);
      if (d > max_dot_mid) {
        max_dot_mid = d;
        best_mid_idx = i;
      }
    }
  }
  std::cout << "Highest dot at mid_norm = " << max_dot_mid << " (Axis " << best_mid_idx << ")\n";

  return 0;
}
