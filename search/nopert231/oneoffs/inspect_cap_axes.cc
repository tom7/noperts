#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

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

  std::cout << "norm_u0: " << norm_u0 << "\n";
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";

  // Check how many axes have center/B close to u0_raw
  int count = 0;
  double max_norm = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    double len_v = yocto::length(v);
    double dot = yocto::dot(u0, yocto::normalize(v));
    if (dot > 0.95) {
      count++;
      max_norm = std::max(max_norm, len_v);
      if (count <= 10) {
        std::cout << "Axis " << i << ": len=" << len_v << ", dot=" << dot
                  << ", delta=" << axes[i].delta.ToDouble() << "\n";
      }
    }
  }
  std::cout << "Total axes with dot > 0.95: " << count << ", max_norm: " << max_norm << "\n";
  return 0;
}
