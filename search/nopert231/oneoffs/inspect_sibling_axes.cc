#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  ContactInfo ax[4][3] = {
    { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14} },
    { {15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9} },
    { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15} },
    { {3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15} }
  };

  for (int j = 1; j <= 3; j++) {
    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri1, ax[j], &cand, 0.0);
    std::cout << "Axis " << j << ": ok=" << ok << ", B=" << std::setprecision(10) << cand.B
              << ", norm_a=(" << cand.normalized_a.x << ", " << cand.normalized_a.y << ", " << cand.normalized_a.z << ")"
              << ", slack=" << cand.strict_slack << "\n";
  }
  return 0;
}
