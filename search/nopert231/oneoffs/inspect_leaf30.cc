#include <iostream>
#include <vector>
#include <string>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "031213002112121221112212122211";
  TriangleQ tri = TriangleFromPath(path);
  std::cout << "Inspecting leaf at depth 30: " << path << "\n";

  vec3 tri_f[3] = {
    ToDouble(tri.corners[0]),
    ToDouble(tri.corners[1]),
    ToDouble(tri.corners[2]),
  };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  std::cout << "Centroid: (" << centroid.x << ", " << centroid.y << ", " << centroid.z << ")\n";

  // Check candidates for centroid view
  auto cands = Tube229::GenerateCandidatesForView(centroid, tri, /*evaluate_over_triangle=*/true, 4, false);
  std::cout << "Candidates generated over triangle: " << cands.size() << "\n";

  if (cands.empty()) {
    std::cout << "No candidates over triangle! Generating at single centroid view...\n";
    auto cands_pt = Tube229::GenerateCandidatesForView(centroid, tri, /*evaluate_over_triangle=*/false, 4, false);
    std::cout << "Candidates at single view: " << cands_pt.size() << "\n";
  }

  // Check closest origin point
  std::vector<vec3> pts;
  for (const auto &c : cands) pts.push_back(c.normalized_a);
  if (!pts.empty()) {
    vec3 cp = Tube229::ClosestOriginPoint(pts);
    double dist = yocto::length(cp);
    std::cout << "Closest point to origin: " << dist << "\n";
  }

  return 0;
}
