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

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double cos_alpha = c_cone / norm_u0;

  // Let's test axes: 391, 3058, 13, 3053, 74, 4893
  std::vector<int> flock_indices = {391, 3058, 13, 3053, 74, 4893};
  std::vector<vec3> flock_v;
  for (int idx : flock_indices) {
    flock_v.push_back(yocto::normalize(vec3{axes[idx].center.x.ToDouble(),
                                            axes[idx].center.y.ToDouble(),
                                            axes[idx].center.z.ToDouble()}));
  }

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double min_max_dot = 1e9;
  int N = 1000000;
  for (int s = 0; s < N; s++) {
    double z = cos_alpha + (1.0 - cos_alpha) * (double)rand() / RAND_MAX;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = 2.0 * M_PI * (double)rand() / RAND_MAX;
    vec3 pt = z * u0 + r * (std::cos(phi) * e1 + std::sin(phi) * e2);

    double max_d = -1e9;
    for (size_t k = 0; k < flock_v.size(); k++) {
      double d = yocto::dot(pt, flock_v[k]);
      if (d > max_d) max_d = d;
    }
    if (max_d < min_max_dot) min_max_dot = max_d;
  }

  std::cout << "1,000,000 random samples in cone:\n";
  std::cout << "Minimum max-dot across the 6 axes: " << min_max_dot << "\n";
  std::cout << "Strictly positive? " << (min_max_dot > 0 ? "YES!" : "NO") << "\n";

  return 0;
}
