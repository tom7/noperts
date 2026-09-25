#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo contacts0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, contacts0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  std::cout << "C++ ctr0 / B: ("
            << ctr0.x.ToDouble() / ax0.B.ToDouble() << ", "
            << ctr0.y.ToDouble() / ax0.B.ToDouble() << ", "
            << ctr0.z.ToDouble() / ax0.B.ToDouble() << ")\n";
  std::cout << "C++ B: " << ax0.B.ToDouble() << "\n";
  return 0;
}
