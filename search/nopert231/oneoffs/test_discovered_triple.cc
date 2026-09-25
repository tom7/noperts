#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  ContactInfo c[3] = {
    // Contact 0: edge 2->1, vertex 2
    {2, 1, 2, 1, 1000, 2},
    // Contact 1: edge 4->8, vertex 4
    {4, 8, 4, 8, 1000, 4},
    // Contact 2: edge 19->3, vertex 19
    {19, 3, 19, 3, 1000, 19}
  };

  Tube229::CandidateTriple cand;
  bool ok = Tube229::DoubleCheckAxis(tri1, c, &cand, 0.0);
  std::cout << "DoubleCheckAxis strict: " << (ok ? "PASS" : "FAIL") << "\n";
  if (ok) {
    std::cout << std::setprecision(12);
    std::cout << "cand.normalized_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
    std::cout << "cand.B = " << cand.B << "\n";
    std::cout << "cand.strict_slack = " << cand.strict_slack << "\n";

    vec3 uncov = {0.401011, -0.483067, -0.778355};
    std::cout << "dot(normalized_a, uncov) = " << yocto::dot(cand.normalized_a, uncov) << "\n";
  }

  return 0;
}
