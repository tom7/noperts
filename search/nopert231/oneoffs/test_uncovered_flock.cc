#include <iostream>
#include <vector>
#include <cmath>
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
  std::string target = "03121303200";
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

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  auto cap_pts = GenerateCapPoints(u0, alpha, 2000);

  vec3 v3054 = yocto::normalize(vec3{axes[3054].center.x.ToDouble(), axes[3054].center.y.ToDouble(), axes[3054].center.z.ToDouble()});
  vec3 v119 = yocto::normalize(vec3{axes[119].center.x.ToDouble(), axes[119].center.y.ToDouble(), axes[119].center.z.ToDouble()});

  // What is the direction perpendicular to u0 along which v3054 is tilted?
  vec3 tilt = yocto::normalize(v3054 - yocto::dot(v3054, u0) * u0);

  double min_dot_3054 = 1e9, max_dot_3054 = -1e9;
  int uncovered_count = 0;
  double min_tilt_uncovered = 1e9, max_tilt_uncovered = -1e9;

  for (const auto &p : cap_pts) {
    double d3054 = yocto::dot(p, v3054);
    min_dot_3054 = std::min(min_dot_3054, d3054);
    max_dot_3054 = std::max(max_dot_3054, d3054);
    if (d3054 < 0.010) {
      uncovered_count++;
      double t = yocto::dot(p, tilt);
      min_tilt_uncovered = std::min(min_tilt_uncovered, t);
      max_tilt_uncovered = std::max(max_tilt_uncovered, t);
    }
  }

  std::cout << "v3054 dot range: [" << min_dot_3054 << ", " << max_dot_3054 << "]\n";
  std::cout << "Uncovered by v3054: " << uncovered_count << " / 2000\n";
  std::cout << "Uncovered points have tilt along v3054 in range: [" << min_tilt_uncovered << ", " << max_tilt_uncovered << "]\n";

  // Check v119 on the uncovered points:
  double min_dot_119 = 1e9;
  for (const auto &p : cap_pts) {
    if (yocto::dot(p, v3054) < 0.010) {
      min_dot_119 = std::min(min_dot_119, yocto::dot(p, v119));
    }
  }
  std::cout << "v119 min dot on uncovered points: " << min_dot_119 << "\n";

  // Check 2-axis cover with v3054 and v119:
  int covered_by_pair = 0;
  for (const auto &p : cap_pts) {
    if (yocto::dot(p, v3054) >= 0.010 || yocto::dot(p, v119) >= 0.010) {
      covered_by_pair++;
    }
  }
  std::cout << "Covered by pair {v3054, v119}: " << covered_by_pair << " / 2000 ("
            << (covered_by_pair * 100.0 / 2000.0) << "%)\n";

  return 0;
}
