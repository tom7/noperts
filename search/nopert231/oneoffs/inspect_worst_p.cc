#include <iostream>
#include <vector>
#include <cmath>
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

  int chosen[4] = {9030, 3449, 389, 36};
  std::vector<vec3> chosen_v;
  for (int idx : chosen) {
    double B = axes[idx].cert.B.ToDouble();
    vec3 v = vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B};
    chosen_v.push_back(v);
    std::cout << "Axis " << idx << ": ||v|| = " << yocto::length(v)
              << ", dot(u0, v) = " << yocto::dot(u0, v)
              << ", angle to u0 = " << (std::acos(yocto::dot(u0, yocto::normalize(v))) * 180.0 / M_PI) << " deg\n";
  }

  return 0;
}
