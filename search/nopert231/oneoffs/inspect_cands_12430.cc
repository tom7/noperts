#include <iostream>
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
  for (int id : {12430, 12435}) {
    std::cout << "--- Cand " << id << " ---\n";
    const auto &c = cands[id];
    for (int j = 0; j < 3; j++) {
      std::cout << "  Contact " << j << ": edge=(" << c.contacts[j].edge_start << "->" << c.contacts[j].edge_finish
                << "), edge2=(" << c.contacts[j].edge_start2 << "->" << c.contacts[j].edge_finish2
                << "), mix=" << c.contacts[j].mix << ", v=" << c.contacts[j].vertex << "\n";
    }
  }
  return 0;
}
