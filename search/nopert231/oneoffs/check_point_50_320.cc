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

  double theta = 50.0 * M_PI / 180.0;
  double phi = 320.0 * M_PI / 180.0;
  vec3 a = std::cos(theta) * u0 + std::sin(theta) * (std::cos(phi) * e1 + std::sin(phi) * e2);

  double max_dot = -1e9;
  int best_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    double d = yocto::dot(a, v);
    if (d > max_dot) {
      max_dot = d;
      best_idx = i;
    }
  }

  std::cout << "At theta = 50 deg, phi = 320 deg:\n";
  std::cout << "  dot(a, u0) = " << yocto::dot(a, u0) << "\n";
  std::cout << "  Max dot with ANY zero-defect axis: " << max_dot << "\n";
  std::cout << "  Best axis index: " << best_idx << "\n";

  return 0;
}
