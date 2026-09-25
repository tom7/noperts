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

  vec3 b1 = yocto::normalize(yocto::cross(u2, vec3{0, 1, 0}));
  vec3 b2 = yocto::cross(u2, b1);

  std::cout << "Testing larger positive offsets along b2:\n";
  double vals[] = {1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 5e-2, 1e-1};

  for (double d2 : vals) {
    vec3 u = yocto::normalize(u2 + d2 * b2);
    auto candidates = Tube229::GenerateCandidatesForView(
        u, tri, false, 8, true);
    std::array<int, 4> simplex;
    vec3 sep_norm;
    bool caged = Tube229::FindBalancedTetrahedron(candidates, &simplex, &sep_norm);
    double norm = yocto::length(sep_norm);
    if (caged) {
      std::cout << "d2 = " << std::setw(7) << d2 << " -> CAGED! (" << candidates.size() << " cands)\n";
    } else {
      std::cout << "d2 = " << std::setw(7) << d2 << " -> FAIL (sep_norm: " << norm << ")\n";
    }
  }

  return 0;
}
