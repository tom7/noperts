#include <iostream>
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
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});

  double target_B[3] = {
    101690303.0 / 500000000.0,
    41861781.0 / 25000000.0,
    128900569.0 / 200000000.0
  };

  for (int m = 0; m < 3; m++) {
    for (size_t i = 0; i < axes.size(); i++) {
      if (std::abs(axes[i].cert.B.ToDouble() - target_B[m]) < 1e-9 && axes[i].cert.contacts[0].mix == (m == 0 ? 1000 : 0)) {
        double B = axes[i].cert.B.ToDouble();
        vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
        vec3 v_norm = yocto::normalize(v);
        std::cout << "Flock " << m << " matches axis " << i << ":\n"
                  << "  B = " << B << "\n"
                  << "  length(center/B) = " << yocto::length(v) << "\n"
                  << "  dot with u0 = " << yocto::dot(u0, v_norm) << "\n"
                  << "  delta = " << axes[i].delta.ToDouble() << "\n";
        break;
      }
    }
  }
  return 0;
}
