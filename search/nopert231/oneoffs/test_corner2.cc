#include <iostream>
#include <vector>

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

  vec3 view = tri_f[2];
  std::cout << "Testing dense candidate search at Corner 2...\n";

  // Dense normal cone samples (e.g. 25 samples)
  auto cands = Tube229::GenerateCandidatesForView(
      view, tri, /*evaluate_over_triangle=*/false, /*cone_samples=*/25, /*include_boundaries=*/true);
  std::cout << "Dense candidates at Corner 2: " << cands.size() << "\n";

  std::array<int, 4> simplex;
  vec3 sep_norm;
  bool caged = Tube229::FindBalancedTetrahedron(cands, &simplex, &sep_norm);
  std::cout << "Corner 2 caged with dense sampling: " << (caged ? "YES" : "NO") << "\n";
  if (!caged) {
    std::cout << "Separating normal: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
    std::cout << "Norm: " << yocto::length(sep_norm) << "\n";
  }

  return 0;
}
