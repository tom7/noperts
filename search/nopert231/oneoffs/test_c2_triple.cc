#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  // Corner 2
  BigVecQ3 c2 = {
    BigRat(53756867, 85983232),
    BigRat(373023, 2686976),
    BigRat(494869, 2097152)
  };
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

  ContactInfo c[3] = {
    {19, 3, 19, 3, 0, 19},
    {4, 8, 4, 8, 0, 4},
    {10, 15, 10, 15, 0, 10}
  };

  Tube229::CandidateTriple cand;
  bool ok = Tube229::DoubleCheckAxis(tri_c2, c, &cand, 0.0);
  std::cout << "DoubleCheckAxis on Corner 2: " << (ok ? "PASS" : "FAIL") << "\n";
  if (ok) {
    std::cout << std::setprecision(10);
    std::cout << "  norm_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
    std::cout << "  slack = " << cand.strict_slack << "\n";
    std::cout << "  B = " << cand.B << "\n";

    vec3 uncov = {0.401011, -0.483067, -0.778355};
    std::cout << "  dot(norm_a, uncov) = " << yocto::dot(cand.normalized_a, uncov) << "\n";
  }

  return 0;
}
