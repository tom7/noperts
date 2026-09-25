#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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

  // Let's sample the cone with 100,000 random points and find the winning axes
  std::vector<vec3> ax_v;
  for (size_t i = 0; i < axes.size(); i++) {
    ax_v.push_back(yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                         axes[i].center.y.ToDouble(),
                                         axes[i].center.z.ToDouble()}));
  }

  // Count how often each axis is the unique best
  std::vector<int> win_count(ax_v.size(), 0);
  int N_samples = 100000;
  for (int s = 0; s < N_samples; s++) {
    // Generate uniform random point in cone
    double z = cos_alpha + (1.0 - cos_alpha) * (double)rand() / RAND_MAX;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = 2.0 * M_PI * (double)rand() / RAND_MAX;
    vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
    vec3 e2 = yocto::cross(u0, e1);
    vec3 pt = z * u0 + r * (std::cos(phi) * e1 + std::sin(phi) * e2);

    int best_i = -1;
    double best_dot = -1e9;
    for (size_t i = 0; i < ax_v.size(); i++) {
      double d = yocto::dot(pt, ax_v[i]);
      if (d > best_dot) {
        best_dot = d;
        best_i = i;
      }
    }
    if (best_i != -1) win_count[best_i]++;
  }

  std::vector<int> winners;
  for (size_t i = 0; i < win_count.size(); i++) {
    if (win_count[i] > 0) {
      winners.push_back(i);
      std::cout << "Axis " << i << " won " << win_count[i] << " times (" << (100.0 * win_count[i] / N_samples) << "%)\n";
    }
  }
  std::cout << "Total winning axes: " << winners.size() << "\n";

  return 0;
}
