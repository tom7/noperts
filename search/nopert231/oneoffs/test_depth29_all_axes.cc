#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  std::string p = "03121300211212201212122222222";
  TriangleQ tri = TriangleFromPath(p);

  ContactInfo axes[4][3] = {
    // Replacement Axis 0
    { {19, 3, 19, 3, 19, 0}, {4, 8, 4, 8, 4, 0}, {10, 15, 10, 15, 10, 0} },
    // Sibling Axis 1
    { {3, 19, 3, 19, 3, 1000}, {1, 2, 1, 2, 1, 1000}, {8, 4, 8, 4, 8, 1000} },
    // Sibling Axis 2
    { {19, 15, 19, 15, 19, 1000}, {1, 1, 4, 1, 4, 1000}, {10, 9, 10, 9, 10, 1000} },
    // Sibling Axis 3
    { {19, 19, 3, 19, 3, 1000}, {2, 2, 1, 2, 1, 1000}, {9, 8, 9, 8, 9, 1000} }
  };

  std::cout << std::setprecision(10);
  for (int a = 0; a < 4; a++) {
    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri, axes[a], &cand, 0.0);
    std::cout << "Axis " << a << ": " << (ok ? "STRICT PASS" : "FAIL")
              << " | slack = " << cand.strict_slack
              << " | norm_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
  }

  return 0;
}
