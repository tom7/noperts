#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  double norm_u0 = std::sqrt((u0.x * u0.x + u0.y * u0.y + u0.z * u0.z).ToDouble());
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  double c_cone = 0.018;
  double cos_alpha = c_cone / norm_u0;

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);

  // Filter zero-defect axes
  std::vector<vec3> zero_v;
  std::vector<int> orig_idx;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      zero_v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
      orig_idx.push_back(i);
    }
  }
  std::cout << "Zero-defect axes tested: " << zero_v.size() << "\n";

  // Generate 2000 test points on C(u0, c_cone)
  std::vector<vec3> cap_pts;
  vec3 z = u0_f;
  vec3 x = yocto::normalize(yocto::cross(z, std::abs(z.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 y = yocto::cross(z, x);
  for (int i = 0; i < 2000; i++) {
    double t = (double)i / 1999.0;
    double cos_theta = 1.0 - t * (1.0 - cos_alpha);
    double sin_theta = std::sqrt(std::max(0.0, 1.0 - cos_theta * cos_theta));
    double phi = i * 2.399963229728653;
    vec3 p = (std::cos(phi) * sin_theta) * x + (std::sin(phi) * sin_theta) * y + cos_theta * z;
    cap_pts.push_back(yocto::normalize(p));
  }

  double best_pair_margin = -1e9;
  int best_pair[2] = {-1, -1};

  for (size_t i = 0; i < zero_v.size(); i++) {
    for (size_t j = i + 1; j < zero_v.size(); j++) {
      double min_max_dot = 1e9;
      for (const auto &p : cap_pts) {
        double d = std::max(yocto::dot(p, zero_v[i]), yocto::dot(p, zero_v[j]));
        min_max_dot = std::min(min_max_dot, d);
      }
      if (min_max_dot > best_pair_margin) {
        best_pair_margin = min_max_dot;
        best_pair[0] = orig_idx[i];
        best_pair[1] = orig_idx[j];
      }
    }
  }

  std::cout << "Best pair (" << best_pair[0] << ", " << best_pair[1] << "): margin = " << best_pair_margin << "\n";
  return 0;
}
