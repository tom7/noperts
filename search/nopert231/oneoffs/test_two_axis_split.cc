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

  int chosen[] = {3054, 119, 3063, 22, 24};
  std::vector<vec3> v;
  for (int idx : chosen) {
    auto &ax = axes[idx];
    v.push_back(yocto::normalize(vec3{ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()}));
  }

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;

  // Let us check all pairs of axes (v[i], v[j]) among the 5 chosen
  // Can a single hyperplane h perpendicular to u0 separate the cap so v[i] covers one half and v[j] covers the other?
  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  for (size_t i = 0; i < v.size(); i++) {
    for (size_t j = i + 1; j < v.size(); j++) {
      // Test 360 separating directions in u0^perp
      for (int deg = 0; deg < 360; deg += 5) {
        double rad = deg * M_PI / 180.0;
        vec3 h = std::cos(rad) * ex + std::sin(rad) * ey;

        // Sample 10,000 points on the cap
        double min_i = 1e9, min_j = 1e9;
        for (int s = 0; s < 10000; s++) {
          double t = (double)s / 9999.0;
          double cos_theta = 1.0 - t * (1.0 - cos_alpha);
          double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
          double phi = s * 2.399963229728653;
          vec3 pt = yocto::normalize((std::cos(phi) * sin_theta) * ex + (std::sin(phi) * sin_theta) * ey + cos_theta * u0);

          if (yocto::dot(pt, h) >= -1e-6) {
            min_i = std::min(min_i, yocto::dot(pt, v[i]));
          }
          if (yocto::dot(pt, h) <= 1e-6) {
            min_j = std::min(min_j, yocto::dot(pt, v[j]));
          }
        }
        if (min_i > 0.005 && min_j > 0.005) {
          std::cout << "FOUND 2-AXIS COVER! Axes (" << chosen[i] << ", " << chosen[j]
                    << ") separated by hyperplane at " << deg << " deg!\n";
          std::cout << "  Half-space 1 (v[" << chosen[i] << "]) min margin: " << min_i << "\n";
          std::cout << "  Half-space 2 (v[" << chosen[j] << "]) min margin: " << min_j << "\n";
          return 0;
        }
      }
    }
  }
  std::cout << "No 2-axis cover found among these 5.\n";
  return 0;
}
