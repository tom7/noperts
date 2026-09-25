#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  // Scan mixes for contact 0, 1, 2 to find the one with minimal max(0, supportUpper)
  double best_defect = 1e9;
  int best_m0 = -1, best_m1 = -1, best_m2 = -1;

  for (int m2 = 0; m2 <= 1000; m2 += 10) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, m2, 14}
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
      // Check maximum positive defect across all vertices
      // In Tube229, AuditAxis returns true if max defect <= 1/1000.
      // Let's compute exact supportUpper:
      // Tube229::ComputeSupportUpper...
      // Or we can check err / audit metrics
    }
  }
  return 0;
}
