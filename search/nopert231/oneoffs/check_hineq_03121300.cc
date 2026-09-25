#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  ContactInfo c_core[3] = {
    {2, 1, 1, 4, 0, 1},
    {14, 15, 15, 19, 500, 15},
    {2, 1, 1, 4, 500, 1}
  };
  AxisCertificate cert_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  Tube229::AuditAxis(tri, c_core, &cert_core, &center_core, &delta_core, &err, BigRat(0));
  vec3 u_core = yocto::normalize(vec3{center_core.x.ToDouble(), center_core.y.ToDouble(), center_core.z.ToDouble()});

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  std::cout << "u_core: (" << u_core.x << ", " << u_core.y << ", " << u_core.z << ")\n";
  double dot = yocto::dot(u0, u_core);
  std::cout << "dot(u0, u_core) = " << dot << " (angle = " << (std::acos(dot) * 180.0 / M_PI) << " deg)\n";

  return 0;
}
