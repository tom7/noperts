#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c[3] = {
    {3, 2, 2, 1, 0, 2},
    {1, 4, 4, 8, 800, 4},
    {10, 15, 15, 19, 333, 15}
  };
  AxisCertificate cert; BigVecQ3 center; BigRat del; std::string err;
  bool ok = Tube229::AuditAxis(tri, c, &cert, &center, &del, &err, BigRat(0));
  std::cout << "AuditAxis with 0 defect: ok=" << ok << ", err=" << err << "\n";
  std::cout << "B = " << cert.B.ToDouble() << ", delta = " << del.ToDouble() << "\n";
  return 0;
}
