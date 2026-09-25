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

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()}) / ax0.B.ToDouble();
  double cos_alpha = c_cone / norm_u0;
  if (cos_alpha > 1.0) cos_alpha = 1.0;
  double sin_alpha = std::sqrt(std::max(0.0, 1.0 - cos_alpha * cos_alpha));

  struct AuditedAxis {
    int id;
    vec3 v;
  };
  std::vector<AuditedAxis> audited;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      audited.push_back({(int)i, v});
    }
  }

  for (int S : {14, 16, 18, 20, 24, 30}) {
    bool all_covered = true;
    for (int s = 0; s < S; s++) {
      double th1 = 2.0 * M_PI * s / S;
      double th2 = 2.0 * M_PI * (s + 1) / S;
      vec3 r0 = u0;
      vec3 r1 = cos_alpha * u0 + sin_alpha * (std::cos(th1) * k1 + std::sin(th1) * k2);
      vec3 r2 = cos_alpha * u0 + sin_alpha * (std::cos(th2) * k1 + std::sin(th2) * k2);

      double best_margin = -1e9;
      for (size_t i = 0; i < audited.size(); i++) {
        double m0 = yocto::dot(r0, audited[i].v);
        double m1 = yocto::dot(r1, audited[i].v);
        double m2 = yocto::dot(r2, audited[i].v);
        double min_m = std::min({m0, m1, m2});
        if (min_m > best_margin) best_margin = min_m;
      }
      if (best_margin < 0.001) {
        all_covered = false;
        break;
      }
    }
    std::cout << "Sectors " << S << ": " << (all_covered ? "ALL COVERED!" : "NOT all covered") << "\n";
  }

  return 0;
}
