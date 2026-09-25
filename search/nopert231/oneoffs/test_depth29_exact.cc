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
    { {19, 3, 19, 3, 1000, 19}, {4, 8, 4, 8, 1000, 4}, {10, 15, 10, 15, 1000, 10} },
    // Sibling Axis 1
    { {3, 19, 3, 19, 1000, 3}, {1, 2, 1, 2, 1000, 1}, {8, 4, 8, 4, 1000, 8} },
    // Sibling Axis 2
    { {19, 15, 19, 15, 1000, 19}, {1, 4, 1, 4, 1000, 1}, {10, 9, 10, 9, 1000, 10} },
    // Sibling Axis 3
    { {19, 3, 19, 3, 1000, 19}, {2, 1, 2, 1, 1000, 2}, {9, 8, 9, 8, 1000, 9} }
  };

  std::cout << std::setprecision(10);
  Tube229::CandidateTriple cands[4];
  for (int a = 0; a < 4; a++) {
    bool ok = Tube229::DoubleCheckAxis(tri, axes[a], &cands[a], 0.0);
    std::cout << "Axis " << a << ": " << (ok ? "STRICT PASS" : "FAIL")
              << " | slack = " << cands[a].strict_slack
              << " | norm_a = (" << cands[a].normalized_a.x << ", "
              << cands[a].normalized_a.y << ", " << cands[a].normalized_a.z << ")\n";
  }

  return 0;
}
