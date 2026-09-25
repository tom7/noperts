#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  BigVecQ3 c2 = tri1.corners[2];
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

  ContactInfo triple[3] = {
    {19, 3, 19, 3, 1000, 19},
    {4, 8, 4, 8, 1000, 4},
    {10, 15, 10, 15, 1000, 15}
  };

  Tube229::CandidateTriple cand;
  bool ok = Tube229::DoubleCheckAxis(tri_c2, triple, &cand, 0.0);
  std::cout << "DoubleCheckAxis on (19, 4, 15): " << (ok ? "PASS" : "FAIL") << "\n";
  if (!ok) {
    // Check which step failed:
    // 1. Check contact validity
    for (int m = 0; m < 3; m++) {
      double slack = 0;
      bool v = Tube229::CheckContactValid(tri_c2, triple[m], &slack);
      std::cout << "  Contact " << m << " valid: " << (v ? "YES" : "NO") << " (slack=" << slack << ")\n";
    }
  } else {
    vec3 uncov = yocto::normalize(vec3{0.401011, -0.483067, -0.778355});
    std::cout << "  norm_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
    std::cout << "  dot(a, uncov) = " << yocto::dot(cand.normalized_a, uncov) << "\n";
    std::cout << "  slack = " << cand.strict_slack << "\n";
  }

  return 0;
}
