#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  std::string B0_str = ax0.B.ToString();
  std::string ctr0_x_str = ctr0.x.ToString();

  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].cert.B.ToString() == B0_str && axes[i].center.x.ToString() == ctr0_x_str) {
      std::cout << "c0_info matched axes[" << i << "]!\n";
      return 0;
    }
  }
  std::cout << "No exact match in axes, B = " << B0_str << "\n";
  return 0;
}
