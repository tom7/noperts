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
  double norm_u0 = yocto::length(u0);
  vec3 dir_u0 = yocto::normalize(u0);

  std::cout << "norm(u0) = " << norm_u0 << "\n";

  double best_cos = -1.0;
  int best_idx = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    vec3 dir_v = yocto::normalize(v);
    double c = yocto::dot(dir_u0, dir_v);
    if (c > best_cos) {
      best_cos = c;
      best_idx = i;
    }
  }

  std::cout << "Best axis idx=" << best_idx << ", cos=" << best_cos << ", angle=" << (std::acos(best_cos) * 180 / M_PI) << " deg\n";
  vec3 v_best = {axes[best_idx].center.x.ToDouble() / axes[best_idx].cert.B.ToDouble(),
                 axes[best_idx].center.y.ToDouble() / axes[best_idx].cert.B.ToDouble(),
                 axes[best_idx].center.z.ToDouble() / axes[best_idx].cert.B.ToDouble()};
  std::cout << "norm(v_best) = " << yocto::length(v_best) << "\n";
  return 0;
}
