#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  std::string p = "031213002112122012121";
  for (int d = 21; d < 31; d++) p += "2";

  TriangleQ tri = TriangleFromPath(p);

  ContactInfo c[3] = {
    {19, 3, 19, 3, 0, 19},
    {4, 8, 4, 8, 0, 4},
    {10, 15, 10, 15, 0, 10}
  };

  Tube229::CandidateTriple cand;
  bool ok = Tube229::DoubleCheckAxis(tri, c, &cand, 0.0);
  std::cout << "Depth 31 cell " << p << ":\n";
  std::cout << "Replacement axis DoubleCheckAxis strict: " << (ok ? "PASS" : "FAIL") << "\n";
  if (ok) {
    std::cout << std::setprecision(12);
    std::cout << "  strict_slack = " << cand.strict_slack << "\n";
    std::cout << "  norm_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
  }

  return 0;
}
