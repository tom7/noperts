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

  double th = 57.95 * M_PI / 180.0;
  double ph = 322.5 * M_PI / 180.0;
  vec3 p = std::cos(th) * u0 + std::sin(th) * (std::cos(ph) * e1 + std::sin(ph) * e2);

  double max_dot = -1e9;
  int best_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    double d = yocto::dot(p, v);
    if (d > max_dot) {
      max_dot = d;
      best_idx = i;
    }
  }

  std::cout << "At theta = 57.95 deg, phi = 322.5 deg:\n";
  std::cout << "  Max dot with ANY zero-defect axis: " << max_dot << "\n";
  std::cout << "  Best axis: " << best_idx << "\n";

  // Also print the top 5 axes:
  std::vector<std::pair<double, int>> ranked;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    ranked.push_back({yocto::dot(p, v), (int)i});
  }
  std::sort(ranked.rbegin(), ranked.rend());
  for (int i = 0; i < 5; i++) {
    std::cout << "    [" << i << "] axis " << ranked[i].second << ": dot = " << ranked[i].first << "\n";
  }

  return 0;
}
