#include <iostream>
#include <vector>
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
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0_raw = vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);

  std::vector<int> flock_indices = {3054, 119, 3063, 22, 24};
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  for (int idx : flock_indices) {
    vec3 v = yocto::normalize(vec3{axes[idx].center.x.ToDouble(), axes[idx].center.y.ToDouble(), axes[idx].center.z.ToDouble()});
    double dot = yocto::dot(u0, v);
    double angle = std::acos(dot) * 180.0 / M_PI;
    std::cout << "Axis " << idx << ": dot(u0, v) = " << dot << " (angle = " << angle << " deg), contacts: ("
              << axes[idx].cert.contacts[0].vertex << ", "
              << axes[idx].cert.contacts[1].vertex << ", "
              << axes[idx].cert.contacts[2].vertex << ")\n";
  }

  return 0;
}
