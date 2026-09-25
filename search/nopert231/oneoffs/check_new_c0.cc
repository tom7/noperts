#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 100, 2},
    {1, 4, 4, 8, 0, 4},
    {13, 14, 14, 15, 1000, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000))) {
    std::cout << "Audit failed: " << err << "\n";
    return 1;
  }

  std::cout << "Audit succeeded!\n";
  std::cout << "del0 = " << del0.ToDouble() << " (" << del0.ToString() << ")\n";
  std::cout << "B0 = " << ax0.B.ToString() << "\n";
  std::cout << "ctr0 = (" << ctr0.x.ToString() << ", " << ctr0.y.ToString() << ", " << ctr0.z.ToString() << ")\n";
  return 0;
}
