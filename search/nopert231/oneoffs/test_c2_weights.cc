#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  BigVecQ3 c2 = {
    BigRat(53756867, 85983232),
    BigRat(373023, 2686976),
    BigRat(494869, 2097152)
  };
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

  ContactInfo axes[4][3] = {
    // Axis 0
    { {19, 3, 19, 3, 0, 19}, {4, 8, 4, 8, 0, 4}, {10, 15, 10, 15, 0, 10} },
    // Axis 1
    { {3, 19, 3, 19, 3, 1000}, {1, 2, 1, 2, 1, 1000}, {8, 4, 8, 4, 8, 1000} },
    // Axis 2
    { {19, 15, 19, 15, 19, 1000}, {1, 1, 4, 1, 4, 1000}, {10, 9, 10, 9, 10, 1000} },
    // Axis 3
    { {19, 19, 3, 19, 3, 1000}, {2, 2, 1, 2, 1, 1000}, {9, 8, 9, 8, 9, 1000} }
  };

  Tube229::CandidateTriple cands[4];
  for (int a = 0; a < 4; a++) {
    bool ok = Tube229::DoubleCheckAxis(tri_c2, axes[a], &cands[a], 0.0);
    std::cout << "Axis " << a << ": " << (ok ? "PASS" : "FAIL")
              << " | norm_a = (" << cands[a].normalized_a.x << ", "
              << cands[a].normalized_a.y << ", " << cands[a].normalized_a.z << ")\n";
  }

  // Barycentric coordinates of 0:
  vec3 p0 = cands[0].normalized_a;
  vec3 p1 = cands[1].normalized_a;
  vec3 p2 = cands[2].normalized_a;
  vec3 p3 = cands[3].normalized_a;

  vec3 a = p0 - p3;
  vec3 b = p1 - p3;
  vec3 c = p2 - p3;
  double det = yocto::dot(a, yocto::cross(b, c));
  vec3 rhs = -p3;
  double w0 = yocto::dot(rhs, yocto::cross(b, c)) / det;
  double w1 = yocto::dot(a, yocto::cross(rhs, c)) / det;
  double w2 = yocto::dot(a, yocto::cross(b, rhs)) / det;
  double w3 = 1.0 - w0 - w1 - w2;

  std::cout << "det = " << det << "\n";
  std::cout << "w0 = " << w0 << ", w1 = " << w1 << ", w2 = " << w2 << ", w3 = " << w3 << "\n";

  return 0;
}
