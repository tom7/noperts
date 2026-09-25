#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}
  };
  ContactInfo c1[3] = {
    {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {2, 1, 1, 4, 333, 1}
  };
  ContactInfo c2[3] = {
    {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 666, 15}, {3, 2, 2, 1, 0, 2}
  };
  ContactInfo c3[3] = {
    {2, 1, 1, 4, 0, 1}, {1, 4, 4, 8, 333, 4}, {15, 19, 19, 3, 1000, 19}
  };

  ContactInfo *all_c[4] = {c0, c1, c2, c3};

  for (int j = 0; j < 4; j++) {
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    Tube229::AuditAxis(tri, all_c[j], &cert, &ctr, &del, &err, BigRat(1, 1000));
    std::cout << "Axis " << j << ": B = " << cert.B.ToDouble()
              << ", delta = " << del.ToDouble()
              << ", err = " << err << "\n";
  }
  return 0;
}
