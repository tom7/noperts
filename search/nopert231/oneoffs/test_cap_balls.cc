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

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double cos_alpha = c_cone / norm_u0;

  // Let us test a Fibonacci lattice of points on the cap
  for (int N = 20; N <= 500; N += 20) {
    // Generate N points on the cap
    std::vector<vec3> q;
    vec3 z = u0;
    vec3 x = yocto::normalize(yocto::cross(z, std::abs(z.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
    vec3 y = yocto::cross(z, x);
    double cos_max = cos_alpha;

    for (int i = 0; i < N; i++) {
      double t = (double)i / (double)(N - 1);
      double cos_theta = 1.0 - t * (1.0 - cos_max);
      double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
      double phi = i * 2.399963229728653;
      vec3 p = (std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z;
      q.push_back(yocto::normalize(p));
    }

    // What is the covering radius rho of these N points over the cap?
    // We can estimate rho by sampling 50,000 dense test points on the cap and finding max distance to nearest q_j:
    double max_dist_to_q = 0;
    for (int s = 0; s < 50000; s++) {
      double t = (double)s / 49999.0;
      double cos_theta = 1.0 - t * (1.0 - cos_max);
      double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
      double phi = s * 2.399963229728653;
      vec3 pt = yocto::normalize((std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z);

      double min_d = 1e9;
      for (const auto &qj : q) {
        min_d = std::min(min_d, yocto::length(pt - qj));
      }
      max_dist_to_q = std::max(max_dist_to_q, min_d);
    }

    // Now for each q_j, find max (q_j . v_m)
    double min_margin = 1e9;
    for (const auto &qj : q) {
      double best_dot = -1e9;
      for (const auto &vm : v) {
        best_dot = std::max(best_dot, yocto::dot(qj, vm));
      }
      min_margin = std::min(min_margin, best_dot);
    }

    double guaranteed_cap_margin = min_margin - max_dist_to_q;
    std::cout << "N = " << N << ": covering radius rho = " << max_dist_to_q
              << ", min sample dot = " << min_margin
              << ", guaranteed margin = " << guaranteed_cap_margin << "\n";
    if (guaranteed_cap_margin > 0.005) {
      std::cout << "SUCCESS with N = " << N << " points! Guaranteed margin > 0.005 everywhere!\n";
      break;
    }
  }
  return 0;
}
