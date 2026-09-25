#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c1[3] = {
    {2, 10, 10, 2, 0, 10},
    {1, 15, 15, 1, 333, 15},
    {4, 19, 19, 4, 333, 19}
  };
  AxisCertificate ax1;
  BigVecQ3 ctr1;
  BigRat del1;
  std::string err;
  if (!Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0))) {
    std::cout << "c1 failed: " << err << "\n";
  } else {
    std::cout << "c1 succeeded!\n";
  }

  ContactInfo c3[3] = {
    {2, 1, 1, 15, 0, 1},
    {1, 4, 4, 19, 333, 4},
    {4, 8, 8, 3, 1000, 8}
  };
  AxisCertificate ax3;
  BigVecQ3 ctr3;
  BigRat del3;
  if (!Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0))) {
    std::cout << "c3 failed: " << err << "\n";
  } else {
    std::cout << "c3 succeeded!\n";
  }
  return 0;
}
