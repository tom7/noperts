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

  ContactInfo flock_contacts[4][3] = {
    {{1, 4, 4, 8, 1000, 4}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 200, 15}},
    {{3, 2, 2, 1, 200, 2}, {1, 4, 4, 8, 1000, 4}, {10, 15, 15, 19, 800, 15}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 200, 15}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 800, 15}, {3, 2, 2, 1, 200, 2}}
  };

  vec3 flock_v[4];
  for (int m = 0; m < 4; m++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, flock_contacts[m], &ax, &ctr, &del, &err, BigRat(1, 1000));
    double B = ax.B.ToDouble();
    flock_v[m] = vec3{ctr.x.ToDouble() / B, ctr.y.ToDouble() / B, ctr.z.ToDouble() / B};
    std::cout << "flock " << m << ": norm = " << yocto::length(flock_v[m]) << ", del = " << del.ToDouble() << "\n";
  }

  for (double c_cone : {0.025, 0.020, 0.015}) {
    double cos_alpha = c_cone / norm_u0;
    double alpha = std::acos(cos_alpha);
    vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
    vec3 k2 = yocto::cross(u0, k1);

    double min_cov = 1e9;
    for (int i = 0; i < 50000; i++) {
      double t = (double)i / 49999.0;
      double r = alpha * std::sqrt(t);
      double phi = i * 2.399963229728653;
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_d = -1e9;
      for (int m = 0; m < 4; m++) {
        max_d = std::max(max_d, (double)yocto::dot(pt, flock_v[m]));
      }
      min_cov = std::min(min_cov, max_d);
    }
    std::cout << "c_cone = " << c_cone << ": min coverage = " << min_cov << "\n";
  }

  return 0;
}
