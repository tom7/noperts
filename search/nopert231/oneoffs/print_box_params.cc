#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::cout << "Triangle path: " << target << "\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  Corner " << i << ": ("
              << tri.corners[i].x.ToDouble() << ", "
              << tri.corners[i].y.ToDouble() << ", "
              << tri.corners[i].z.ToDouble() << ")\n";
  }

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  std::cout << "B0 = " << ax0.B.ToDouble() << "\n";
  std::cout << "del0 = " << del0.ToDouble() << "\n";
  std::cout << "ctr0 norm = " << yocto::length(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()}) << "\n";

  vec2 c0 = vec2{tri.corners[0].x.ToDouble() / tri.corners[0].z.ToDouble(), tri.corners[0].y.ToDouble() / tri.corners[0].z.ToDouble()};
  vec2 c1 = vec2{tri.corners[1].x.ToDouble() / tri.corners[1].z.ToDouble(), tri.corners[1].y.ToDouble() / tri.corners[1].z.ToDouble()};
  vec2 c2 = vec2{tri.corners[2].x.ToDouble() / tri.corners[2].z.ToDouble(), tri.corners[2].y.ToDouble() / tri.corners[2].z.ToDouble()};
  vec2 mid = (c0 + c1 + c2) / 3.0;
  double r = std::max({yocto::length(c0 - mid), yocto::length(c1 - mid), yocto::length(c2 - mid)}) * 2.0;
  std::cout << "box.r approx = " << r << "\n";

  return 0;
}
