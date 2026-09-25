#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303022";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo cont0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14} // annular axis
  };

  ContactInfo cont_hull[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {10, 15, 15, 19, 800, 15} // true hull axis
  };

  AxisCertificate ax0, ax_hull;
  BigVecQ3 c0, c_hull;
  BigRat d0, d_hull;
  std::string err;

  Tube229::AuditAxis(tri, cont0, &ax0, &c0, &d0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, cont_hull, &ax_hull, &c_hull, &d_hull, &err, BigRat(0));

  vec3 dir0 = yocto::normalize(vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()});
  vec3 dir_h = yocto::normalize(vec3{c_hull.x.ToDouble(), c_hull.y.ToDouble(), c_hull.z.ToDouble()});

  double dot = yocto::dot(dir0, dir_h);
  double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;

  std::cout << "annular axis: B = " << ax0.B.ToDouble() << " dir = (" << dir0.x << ", " << dir0.y << ", " << dir0.z << ")\n";
  std::cout << "true hull axis: B = " << ax_hull.B.ToDouble() << " dir = (" << dir_h.x << ", " << dir_h.y << ", " << dir_h.z << ")\n";
  std::cout << "Angle between annular axis and true hull axis: " << angle << " deg\n";
  std::cout << "Dot product: " << dot << "\n";

  return 0;
}
