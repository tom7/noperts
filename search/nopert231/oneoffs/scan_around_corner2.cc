#include <iostream>
#include <iomanip>
#include <vector>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"

using namespace tubetree229;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 c2 = vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()};
  vec3 u2 = yocto::normalize(c2);

  // Basis orthogonal to u2
  vec3 b1 = yocto::normalize(yocto::cross(u2, vec3{0, 1, 0}));
  vec3 b2 = yocto::cross(u2, b1);

  std::cout << "Scanning grid of views around Corner 2 to see where origin is caged pointwise:\n";
  std::cout << "Corner 2 view: (" << u2.x << ", " << u2.y << ", " << u2.z << ")\n\n";

  // Scan in steps of 1e-6 radians (approx depth 20-21 scale) and 1e-8 radians (approx depth 28 scale)
  double steps[] = {-1e-6, -1e-7, -1e-8, 0.0, 1e-8, 1e-7, 1e-6};

  for (double d1 : steps) {
    for (double d2 : steps) {
      vec3 u = yocto::normalize(u2 + d1 * b1 + d2 * b2);

      // Generate candidates at this exact view
      auto candidates = Tube229::GenerateCandidatesForView(
          u, tri, /*evaluate_over_triangle=*/false, /*cone_samples=*/8, /*include_boundaries=*/true);

      std::array<int, 4> simplex;
      vec3 sep_norm;
      bool caged = Tube229::FindBalancedTetrahedron(candidates, &simplex, &sep_norm);

      double norm = yocto::length(sep_norm);
      if (caged) {
        std::cout << "d1=" << std::setw(7) << d1 << " d2=" << std::setw(7) << d2
                  << " -> CAGED! (" << candidates.size() << " candidates)\n";
      } else {
        std::cout << "d1=" << std::setw(7) << d1 << " d2=" << std::setw(7) << d2
                  << " -> FAIL (sep_norm: " << norm << ")\n";
      }
    }
  }

  return 0;
}
