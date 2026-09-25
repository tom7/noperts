#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  // Original Axis 0 contacts:
  // c0: {3, 2, 2, 1, 800, 2}
  // c1: {1, 4, 4, 8, 800, 4}
  // c2: {13, 14, 14, 15, 200, 14}
  
  std::cout << "Testing different mix values for contact 2:\n";
  for (int m2 = 0; m2 <= 300; m2 += 10) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, m2, 14}
    };
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
      std::cout << "m2 = " << m2 << ": B = " << cert.B.ToDouble()
                << ", delta = " << del.ToDouble()
                << ", center = (" << ctr.x.ToDouble() << ", " << ctr.y.ToDouble() << ", " << ctr.z.ToDouble() << ")\n";
    } else {
      std::cout << "m2 = " << m2 << ": FAILED: " << err << "\n";
    }
  }
  return 0;
}
