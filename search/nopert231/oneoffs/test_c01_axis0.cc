#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  // Original Axis 0 from sibling
  ContactInfo axis0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  std::cout << std::setprecision(10);
  for (int cr = 0; cr < 3; cr++) {
    TriangleQ tri_corner;
    tri_corner.corners[0] = tri1.corners[cr];
    tri_corner.corners[1] = tri1.corners[cr];
    tri_corner.corners[2] = tri1.corners[cr];

    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri_corner, axis0, &cand, 0.0);
    std::cout << "Corner " << cr << ": " << (ok ? "PASS" : "FAIL")
              << " | slack = " << cand.strict_slack << "\n";
  }

  return 0;
}
