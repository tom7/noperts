#include <iostream>
#include <vector>
#include <string>

#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"

using namespace tubetree229;
using CandidateTriple = Tube229::CandidateTriple;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 tri_f[3] = {
    vec3{tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()},
    vec3{tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()},
    vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()},
  };
  vec3 centroid = yocto::normalize((tri_f[0] + tri_f[1] + tri_f[2]) / 3.0);

  std::vector<vec3> sample_views = {centroid, tri_f[0], tri_f[1], tri_f[2]};
  std::vector<CandidateTriple> candidates;
  for (const auto &view : sample_views) {
    auto v_cands = Tube229::GenerateCandidatesForView(view, tri, true, 4, false);
    for (const auto &c : v_cands) {
      // Deduplicate
      bool exists = false;
      for (const auto &existing : candidates) {
        if (existing.contacts[0].vertex == c.contacts[0].vertex &&
            existing.contacts[1].vertex == c.contacts[1].vertex &&
            existing.contacts[2].vertex == c.contacts[2].vertex &&
            existing.contacts[0].mix == c.contacts[0].mix &&
            existing.contacts[1].mix == c.contacts[1].mix &&
            existing.contacts[2].mix == c.contacts[2].mix) {
          exists = true;
          break;
        }
      }
      if (!exists) candidates.push_back(c);
    }
  }

  std::cout << "Total deduplicated candidates over all 4 sample views: " << candidates.size() << "\n";

  std::array<int, 4> simplex;
  vec3 sep_norm;
  bool caged = Tube229::FindBalancedTetrahedron(candidates, &simplex, &sep_norm);

  if (caged) {
    std::cout << "SUCCESS: Origin is enclosed! Simplex: "
              << simplex[0] << ", " << simplex[1] << ", " << simplex[2] << ", " << simplex[3] << "\n";
  } else {
    std::cout << "FAILED to enclose origin.\n";
    std::cout << "Separating normal: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
    std::cout << "Norm length: " << yocto::length(sep_norm) << "\n";

    // Check which candidates come closest to opposing sep_norm (dot product < 0)
    std::cout << "Top candidates along -sep_norm:\n";
    std::vector<std::pair<double, int>> dots;
    vec3 unit_sep = yocto::normalize(sep_norm);
    for (size_t i = 0; i < candidates.size(); i++) {
      double d = yocto::dot(candidates[i].normalized_a, unit_sep);
      dots.push_back({d, (int)i});
    }
    std::sort(dots.begin(), dots.end());
    for (int i = 0; i < std::min(10, (int)dots.size()); i++) {
      int idx = dots[i].second;
      const auto &c = candidates[idx];
      std::cout << "  dot=" << dots[i].first << " : vertices {"
                << c.contacts[0].vertex << ", " << c.contacts[1].vertex << ", " << c.contacts[2].vertex << "}"
                << " mixes {" << c.contacts[0].mix << ", " << c.contacts[1].mix << ", " << c.contacts[2].mix << "}\n";
    }
  }

  return 0;
}
