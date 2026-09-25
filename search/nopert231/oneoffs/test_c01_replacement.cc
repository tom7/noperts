#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  // Replacement Axis 0
  ContactInfo repl[3] = {
    {19, 3, 19, 3, 0, 19},
    {4, 8, 4, 8, 0, 4},
    {10, 15, 10, 15, 0, 10}
  };

  std::cout << std::setprecision(10);
  for (int cr = 0; cr < 3; cr++) {
    TriangleQ tri_corner;
    tri_corner.corners[0] = tri1.corners[cr];
    tri_corner.corners[1] = tri1.corners[cr];
    tri_corner.corners[2] = tri1.corners[cr];

    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri_corner, repl, &cand, 0.0);
    std::cout << "Corner " << cr << ": " << (ok ? "PASS" : "FAIL")
              << " | slack = " << cand.strict_slack << "\n";
  }

  return 0;
}
