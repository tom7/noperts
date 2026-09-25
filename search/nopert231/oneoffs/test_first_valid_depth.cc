#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  std::string p = "031213002112122012121";
  ContactInfo c[3] = {
    {19, 3, 19, 3, 0, 19},
    {4, 8, 4, 8, 0, 4},
    {10, 15, 10, 15, 0, 10}
  };

  for (int d = 21; d <= 31; d++) {
    TriangleQ tri = TriangleFromPath(p);
    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri, c, &cand, 0.0);
    std::cout << "Depth " << d << " (" << p << "): "
              << (ok ? "STRICT PASS" : "FAIL")
              << " | slack = " << cand.strict_slack << "\n";
    p += "2";
  }

  return 0;
}
