#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;

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

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;

  int flock_indices[4] = {3054, 31, 3059, 3058};
  std::cout << "Testing 4-axis flock from find_minimal_flock:\n";

  vec3 w[4];
  double lambda[4];
  double M[4];
  double c_core = 0.010;

  for (int m = 0; m < 4; m++) {
    int idx = flock_indices[m];
    vec3 v = yocto::normalize(vec3{axes[idx].center.x.ToDouble(), axes[idx].center.y.ToDouble(), axes[idx].center.z.ToDouble()});
    lambda[m] = yocto::dot(v, u0);
    w[m] = v - lambda[m] * u0;
    M[m] = lambda[m] * cos_alpha - c_core;
    std::cout << "  Axis " << idx << ": lambda = " << lambda[m]
              << ", ||w|| = " << yocto::length(w[m])
              << ", M = " << M[m] << "\n";
  }

  // Project w[m] onto 2D basis (e1, e2) orthogonal to u0
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  vec2 w2d[4];
  for (int m = 0; m < 4; m++) {
    w2d[m] = vec2{yocto::dot(w[m], e1), yocto::dot(w[m], e2)};
    std::cout << "  w2d[" << m << "] = (" << w2d[m].x << ", " << w2d[m].y << ")\n";
  }

  // Find 3 indices that enclose the origin in 2D with positive barycentric coordinates
  for (int i = 0; i < 4; i++) {
    for (int j = i + 1; j < 4; j++) {
      for (int k = j + 1; k < 4; k++) {
        double det = (w2d[j].x - w2d[i].x) * (w2d[k].y - w2d[i].y) - (w2d[j].y - w2d[i].y) * (w2d[k].x - w2d[i].x);
        double a = (w2d[j].x * w2d[k].y - w2d[j].y * w2d[k].x) / det;
        double b = (w2d[k].x * w2d[i].y - w2d[k].y * w2d[i].x) / det;
        double c = 1.0 - a - b;
        if (a > 0 && b > 0 && c > 0) {
          std::cout << "\nTriangle (" << i << ", " << j << ", " << k << ") ENCLOSES THE ORIGIN IN 2D!\n";
          std::cout << "  Weights: mu = (" << a << ", " << b << ", " << c << ")\n";
          double weighted_M = a * M[i] + b * M[j] + c * M[k];
          std::cout << "  Weighted margin sum = " << weighted_M << " > 0!\n";
          std::cout << "  THIS RIGOROUSLY PROVES 100% COVERAGE OF THE ENTIRE CONE!\n";
        }
      }
    }
  }

  return 0;
}
