#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_ann[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c_ann, &cert0, &center0, &delta0, &err, BigRat(5, 1000));

  std::cout << "center0: (" << center0.x.ToDouble() << ", " << center0.y.ToDouble() << ", " << center0.z.ToDouble() << ")\n";
  std::cout << "B0: " << cert0.B.ToDouble() << "\n";

  vec3 u0 = {center0.x.ToDouble() / cert0.B.ToDouble(),
             center0.y.ToDouble() / cert0.B.ToDouble(),
             center0.z.ToDouble() / cert0.B.ToDouble()};
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  std::cout << "|u0|^2: " << yocto::dot(u0, u0) << "\n";
  std::cout << "|center0|^2: " << yocto::dot(vec3{center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()},
                                              vec3{center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()}) << "\n";
  return 0;
}
