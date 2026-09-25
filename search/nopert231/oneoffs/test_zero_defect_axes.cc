#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Found " << axes.size() << " zero-defect axes!\n";

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = {ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  // Find the zero-defect axis closest in angle to dir_u0:
  double max_dot = -1.0;
  size_t best_idx = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(yocto::normalize(v), dir_u0);
    if (d > max_dot) {
      max_dot = d;
      best_idx = i;
    }
  }

  std::cout << "Closest zero-defect axis to u0: idx=" << best_idx
            << ", dot=" << max_dot << ", angle=" << (std::acos(max_dot) * 180.0 / M_PI) << " deg\n";
  return 0;
}
