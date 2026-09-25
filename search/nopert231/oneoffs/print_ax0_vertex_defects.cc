#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  std::cout << "del0 = " << del0.ToDouble() << "\n";
  std::cout << "B0 = " << ax0.B.ToDouble() << "\n";

  // Check supportUpper for each contact i in {0,1,2} and each vertex k in {0..23}
  // In Lean: supportUpper j i k = (c - v_k) . (contact normal) ...
  // Wait, AuditAxis does this! Let's see what AuditAxis computes:
  return 0;
}
