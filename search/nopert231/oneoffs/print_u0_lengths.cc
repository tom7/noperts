#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c1[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax1; BigVecQ3 ctr1; BigRat del1; std::string err;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(5, 1000));
  vec3 u1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(),
             ctr1.y.ToDouble() / ax1.B.ToDouble(),
             ctr1.z.ToDouble() / ax1.B.ToDouble()};
  std::cout << "Axis 1 (mix 200 on 14): ||u1|| = " << yocto::length(u1)
            << ", 4/7 * ||u1|| = " << (4.0 / 7.0) * yocto::length(u1) << "\n";

  ContactInfo c2[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {14, 15, 15, 19, 900, 15}
  };
  AxisCertificate ax2; BigVecQ3 ctr2; BigRat del2;
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(5, 1000));
  vec3 u2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(),
             ctr2.y.ToDouble() / ax2.B.ToDouble(),
             ctr2.z.ToDouble() / ax2.B.ToDouble()};
  std::cout << "Axis 2 (mix 900 on 15): ||u2|| = " << yocto::length(u2)
            << ", 4/7 * ||u2|| = " << (4.0 / 7.0) * yocto::length(u2) << "\n";
  return 0;
}
