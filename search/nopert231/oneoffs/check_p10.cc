#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  int N_sectors = 32;
  int N_rings = 8;
  int r = 5;
  int s = 28;
  double theta1 = (double)(r + 1) / N_rings * alpha;
  double phi0 = 2.0 * M_PI * s / N_sectors;

  vec3 p10 = std::cos(theta1) * u0 + std::sin(theta1) * (std::cos(phi0) * e1 + std::sin(phi0) * e2);

  double max_dot = -1e9;
  int best_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    double d = yocto::dot(p10, v);
    if (d > max_dot) {
      max_dot = d;
      best_idx = i;
    }
  }

  std::cout << "For vertex p10 (theta = " << theta1 * 180 / M_PI << ", phi = " << phi0 * 180 / M_PI << "):\n";
  std::cout << "  Max dot: " << max_dot << "\n";
  std::cout << "  Best axis index: " << best_idx << "\n";

  return 0;
}
