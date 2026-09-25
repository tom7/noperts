#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

std::vector<vec3> GenerateCapPoints(const vec3 &u0, double alpha_rad, int num_points) {
  std::vector<vec3> pts;
  vec3 z = u0;
  vec3 x = yocto::normalize(yocto::cross(z, std::abs(z.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 y = yocto::cross(z, x);

  double cos_max = std::cos(alpha_rad);
  for (int i = 0; i < num_points; i++) {
    double t = (double)i / (double)(num_points - 1);
    double cos_theta = 1.0 - t * (1.0 - cos_max);
    double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
    double phi = i * 2.399963229728653;
    vec3 p = (std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z;
    pts.push_back(yocto::normalize(p));
  }
  return pts;
}

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
  vec3 u0_raw = vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    all_v.push_back(v);
  }
  std::cout << "Audited " << all_v.size() << " zero-defect axes.\n";

  for (double c_cone : {0.010, 0.015, 0.020, 0.025, 0.030}) {
    double cos_alpha = c_cone / norm_u0;
    if (cos_alpha > 1.0) continue;
    double alpha = std::acos(cos_alpha);
    auto cap_pts = GenerateCapPoints(u0, alpha, 2000);

    double min_over_cap = 1e9;
    int uncovered = 0;
    for (const auto &p : cap_pts) {
      double max_dot = -1e9;
      for (const auto &v : all_v) {
        double d = yocto::dot(p, v);
        if (d > max_dot) max_dot = d;
      }
      if (max_dot < min_over_cap) min_over_cap = max_dot;
      if (max_dot <= 0) uncovered++;
    }
    std::cout << "c_cone = " << c_cone << " (alpha = " << alpha * 180.0 / M_PI << " deg): "
              << "min_margin = " << min_over_cap << ", uncovered = " << uncovered << " / 2000\n";
  }

  return 0;
}
