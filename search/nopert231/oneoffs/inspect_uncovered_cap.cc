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

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  std::cout << "Testing c_cone = " << c_cone << ", alpha = " << alpha * 180.0 / M_PI << " deg:\n";

  // Filter all candidate axes in the ENTIRE pool of 9307 axes
  // What is the max delta among valid axes?
  // Let's check without delta filter first: what is max dot with uncovered points?
  int chosen[] = {9030, 36, 8815, 3065, 8663};
  std::vector<vec3> flock_v;
  for (int idx : chosen) {
    double B = axes[idx].cert.B.ToDouble();
    flock_v.push_back(vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B});
  }

  // Generate 5000 points on the 60.7 deg cap
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double min_cov = 1e9;
  vec3 worst_pt;
  for (int i = 0; i < 5000; i++) {
    double t = (double)i / 4999.0;
    double r = alpha * std::sqrt(t);
    double phi = i * 2.399963229728653;
    vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
    double max_m = -1e9;
    for (const auto &v : flock_v) max_m = std::max(max_m, yocto::dot(pt, v));
    if (max_m < min_cov) {
      min_cov = max_m;
      worst_pt = pt;
    }
  }

  std::cout << "Min cover with first 5 axes: " << min_cov << "\n";
  std::cout << "Worst point dot with u0: " << yocto::dot(worst_pt, u0) << "\n";

  // Now find the best axis in the entire axes pool for worst_pt
  int best_axis = -1;
  double best_dot = -1e9;
  for (size_t i = 0; i < axes.size(); i++) {
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    double d = yocto::dot(worst_pt, v);
    if (d > best_dot) {
      best_dot = d;
      best_axis = i;
    }
  }
  std::cout << "Best axis in entire pool for worst_pt: Axis " << best_axis
            << ", dot = " << best_dot
            << ", delta = " << axes[best_axis].delta.ToDouble() << "\n";

  return 0;
}
