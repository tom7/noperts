#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo new_c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {8, 9, 9, 10, 0, 9}
  };
  AxisCertificate c0_cert; BigVecQ3 c0_ctr; BigRat c0_del; std::string err;
  Tube229::AuditAxis(tri, new_c0, &c0_cert, &c0_ctr, &c0_del, &err, BigRat(0));
  vec3 u0 = {c0_ctr.x.ToDouble() / c0_cert.B.ToDouble(),
             c0_ctr.y.ToDouble() / c0_cert.B.ToDouble(),
             c0_ctr.z.ToDouble() / c0_cert.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  double min_angle = 180.0;
  int min_idx = -1;

  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 u = {ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
      vec3 u_dir = yocto::normalize(u);
      double dot = yocto::dot(u0_dir, u_dir);
      double angle = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
      if (angle < min_angle) {
        min_angle = angle;
        min_idx = i;
      }
    }
  }

  std::cout << "Min angle to new u0: " << min_angle << " deg (axis " << min_idx << ")\n";
  return 0;
}
