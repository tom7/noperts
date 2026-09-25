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
  vec3 u0 = vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()};

  double c_core = 0.005;
  double c_cone = 0.015;
  double S = (c_core + 0.001) / c_cone;
  vec3 pseudo_u0 = -S * u0;

  std::vector<vec3> all_pts;
  all_pts.push_back(pseudo_u0);
  for (size_t i = 0; i < axes.size(); i++) {
    all_pts.push_back(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
  }

  // Find min over unit normal n of (max_i dot(n, P_i))
  // This is the inradius of conv(all_pts)!
  double min_support = 1e9;
  vec3 worst_n;
  for (int trial = 0; trial < 100000; trial++) {
    double z = 2.0 * ((double)rand() / RAND_MAX) - 1.0;
    double phi = 2.0 * M_PI * ((double)rand() / RAND_MAX);
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    vec3 n{r * std::cos(phi), r * std::sin(phi), z};

    double max_dot = -1e9;
    for (const auto &p : all_pts) {
      double d = yocto::dot(n, p);
      if (d > max_dot) max_dot = d;
    }
    if (max_dot < min_support) {
      min_support = max_dot;
      worst_n = n;
    }
  }

  std::cout << "Inradius of conv({pseudo_u0, zero_defect_axes}): " << min_support << "\n";
  std::cout << "Worst normal: (" << worst_n.x << ", " << worst_n.y << ", " << worst_n.z << ")\n";
  std::cout << "dot(worst_n, u0): " << yocto::dot(worst_n, u0) << "\n";

  return 0;
}
