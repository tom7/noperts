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

  vec3 pt = yocto::normalize(vec3{0.402, -0.480, -0.785});
  std::cout << "Testing pt = (" << pt.x << ", " << pt.y << ", " << pt.z << ")\n";

  int chosen[] = {3063, 22, 24, 3054, 119};
  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del; std::string err;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    std::cout << "  Axis " << idx << ": dot = " << yocto::dot(pt, v) << "\n";
  }

  // Find maximum dot over ALL zero-defect axes:
  double max_d = -1e9;
  int max_idx = -1;
  vec3 max_v;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del; std::string err;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      double d = yocto::dot(pt, v);
      if (d > max_d) {
        max_d = d;
        max_idx = i;
        max_v = v;
      }
    }
  }
  std::cout << "Best over ALL zero-defect axes: dot = " << max_d << " (Axis " << max_idx << ")\n";
  std::cout << "Best axis v = (" << max_v.x << ", " << max_v.y << ", " << max_v.z << ")\n";
  return 0;
}
