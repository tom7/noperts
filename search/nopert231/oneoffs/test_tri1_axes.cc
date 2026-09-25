#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  ContactInfo c[3] = {
    {2, 3, 2, 3, 2, 1000},
    {4, 4, 8, 4, 8, 1000},
    {15, 15, 19, 15, 19, 1000}
  };

  Tube229::CandidateTriple cand;
  // screen_support_error = 1e-8 allows 2.26e-9 defect!
  bool ok = Tube229::DoubleCheckAxis(tri1, c, &cand, 1e-8);
  std::cout << "DoubleCheckAxis with tolerance 1e-8: " << (ok ? "PASS" : "FAIL") << "\n";
  if (ok) {
    std::cout << std::setprecision(12);
    std::cout << "cand.normalized_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
    std::cout << "cand.B = " << cand.B << "\n";
    std::cout << "cand.strict_slack = " << cand.strict_slack << "\n";

    vec3 sep_norm = {-0.401011, 0.483067, 0.778355};
    std::cout << "dot(normalized_a, sep_norm) = " << yocto::dot(cand.normalized_a, sep_norm) << "\n";
  }
  return 0;
}
