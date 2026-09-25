#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  vec3 v = yocto::normalize(vec3{axes[391].center.x.ToDouble(),
                                axes[391].center.y.ToDouble(),
                                axes[391].center.z.ToDouble()});
  double lam = yocto::dot(u0, v);
  double d1 = yocto::dot(e1, v);
  double d2 = yocto::dot(e2, v);
  double mu = std::sqrt(d1 * d1 + d2 * d2);
  double psi = std::atan2(d2, d1);

  std::cout << "Axis 391:\n";
  std::cout << "  lam = " << lam << ", mu = " << mu << ", psi = " << psi * 180 / M_PI << " deg\n";

  return 0;
}
