#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

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

  double x = 1.26511, y = -0.969618;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  ContactInfo best_triple[3] = {
    {8, 9, 9, 10, 0, 9},
    {9, 10, 10, 15, 1000, 10},
    {9, 10, 10, 13, 1000, 10}
  };

  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  if (Tube229::AuditAxis(tri, best_triple, &cert, &center, &delta, &err, BigRat(1, 1000))) {
    std::cout << "AuditAxis SUCCESS!\n";
    vec3 v = yocto::normalize(vec3{center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
    std::cout << "Center v: (" << v.x << ", " << v.y << ", " << v.z << ")\n";
    std::cout << "Dot(v, p) = " << yocto::dot(v, p) << "\n";
    std::cout << "delta = " << delta.ToDouble() << "\n";
    std::cout << "B = " << cert.B.ToDouble() << "\n";
    // Check support upper bounds
    for (int i = 0; i < 3; i++) {
      std::cout << "  contact " << i << " supportUpper: ";
      for (int k = 0; k < 3; k++) {
      }
      std::cout << "\n";
    }
  } else {
    std::cout << "AuditAxis FAILED: " << err << "\n";
  }

  return 0;
}
