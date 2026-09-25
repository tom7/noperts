#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 centroid = vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  };

  auto cands = Tube229::GenerateCandidatesForView(centroid, tri, true, 4, true, 1e-12);
  std::vector<int> flock_indices = {14060, 2344, 4688, 7032, 9376, 11720};
  for (int idx : flock_indices) {
    vec3 v = cands[idx].normalized_a;
    std::cout << "Cand " << idx << ": v = (" << v.x << ", " << v.y << ", " << v.z << "), norm=" << yocto::length(v) << "\n";
  }
  return 0;
}
