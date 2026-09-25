#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Found " << axes.size() << " audited zero-defect axes!\n";

  // Annular axis u0 from row 3253
  // Contacts: (3,2), (1,4), (13,14/14,15)
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
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";

  int count_close = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    double dot = yocto::dot(u0, v);
    double deg = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
    if (deg < 90.0) {
      count_close++;
      std::cout << "  Axis " << i << ": angle = " << deg << " deg, v = ("
                << v.x << ", " << v.y << ", " << v.z << "), contacts: ("
                << axes[i].cert.contacts[0].vertex << ", "
                << axes[i].cert.contacts[1].vertex << ", "
                << axes[i].cert.contacts[2].vertex << ")\n";
    }
  }
  std::cout << "Total axes with angle < 90 deg: " << count_close << "\n";
  return 0;
}
