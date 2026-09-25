#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  double min_defect = 1e9;
  int best_mix = -1;

  for (int mix = 0; mix <= 1000; mix += 10) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, mix, 14}
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
      // Find max defect across 24 vertices
      double max_def = 0.0;
      for (int k = 0; k < 20; k++) {
        BigRat s = ax.supportUpper[2][k];
        if (s.ToDouble() > max_def) max_def = s.ToDouble();
      }
      std::cout << "mix = " << mix << ", B = " << ax.B.ToDouble() << ", max_def = " << max_def << "\n";
    }
  }

  return 0;
}
