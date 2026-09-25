#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  
  // Axes 0, 1, 2, 3 from sibling n0:
  ContactInfo axes[4][3] = {
    // Axis 0
    { {2, 3, 2, 3, 2, 1000}, {4, 4, 8, 4, 8, 1000}, {15, 15, 19, 15, 19, 1000} },
    // Axis 1
    { {3, 19, 3, 19, 3, 1000}, {1, 2, 1, 2, 1, 1000}, {8, 4, 8, 4, 8, 1000} },
    // Axis 2
    { {19, 15, 19, 15, 19, 1000}, {1, 1, 4, 1, 4, 1000}, {10, 9, 10, 9, 10, 1000} },
    // Axis 3
    { {19, 19, 3, 19, 3, 1000}, {2, 2, 1, 2, 1, 1000}, {9, 8, 9, 8, 9, 1000} }
  };

  std::cout << std::setprecision(12);
  Tube229::CandidateTriple cands[4];

  for (int a = 0; a < 4; a++) {
    bool ok_strict = Tube229::DoubleCheckAxis(tri1, axes[a], &cands[a], 0.0);
    bool ok_tol = Tube229::DoubleCheckAxis(tri1, axes[a], &cands[a], 1e-8);
    std::cout << "Axis " << a << ": strict=" << (ok_strict ? "PASS" : "FAIL")
              << ", tol(1e-8)=" << (ok_tol ? "PASS" : "FAIL")
              << " | norm_a = (" << cands[a].normalized_a.x << ", "
              << cands[a].normalized_a.y << ", " << cands[a].normalized_a.z << ")"
              << " | slack = " << cands[a].strict_slack << "\n";
  }

  return 0;
}
