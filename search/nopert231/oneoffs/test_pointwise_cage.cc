#include <iostream>
#include <vector>
#include <string>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"

using namespace tubetree229;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 tri_f[3] = {
    vec3{tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()},
    vec3{tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()},
    vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()},
  };

  std::cout << "Inspecting Corner 2 pointwise candidates:\n";
  auto c_cands = Tube229::GenerateCandidatesForView(
      tri_f[2], tri, /*evaluate_over_triangle=*/false, /*cone_samples=*/10, /*include_boundaries=*/true);
  std::cout << "Total candidates: " << c_cands.size() << "\n";

  std::array<int, 4> simplex;
  vec3 sep_norm;
  bool c_caged = Tube229::FindBalancedTetrahedron(c_cands, &simplex, &sep_norm);
  std::cout << "Caged: " << (c_caged ? "YES" : "NO") << "\n";
  std::cout << "Separating normal: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
  std::cout << "Norm: " << yocto::length(sep_norm) << "\n";

  // Check 2D hull at Corner 2
  vec3 axis = vec3{0, 1, 0};
  vec3 first = yocto::normalize(yocto::cross(tri_f[2], axis));
  vec3 second = yocto::cross(tri_f[2], first);
  std::vector<Tube229::vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = Tube229::vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> hull = Tube229::ConvexHull2D(projected);
  std::cout << "2D Convex Hull at Corner 2:\n";
  for (int h : hull) {
    std::cout << "  v" << h << "\n";
  }

  return 0;
}
