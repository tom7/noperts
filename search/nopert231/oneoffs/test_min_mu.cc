#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  for (const auto &ax : hull_axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
  std::cout << "Hull valid axes: " << valid_axes.size() << "\n";

  for (size_t i = 0; i < valid_axes.size(); i++) {
    double B = valid_axes[i].cert.B.ToDouble();
    vec3 vi = vec3{valid_axes[i].center.x.ToDouble() / B,
                   valid_axes[i].center.y.ToDouble() / B,
                   valid_axes[i].center.z.ToDouble() / B};
    double cos_ang = yocto::dot(u0, vi) / (yocto::length(u0) * yocto::length(vi));
    if (cos_ang > 0.98) {
      std::cout << "Axis " << i << " cos_ang = " << cos_ang << "\n";
    }
  }
  return 0;
}
