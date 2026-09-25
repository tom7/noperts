#include <iostream>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  vec3 centroid = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;

  std::vector<int> fine_mixes;
  for (int m = 0; m <= 1000; m += 20) fine_mixes.push_back(m);

  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  bool has_0_4 = false;
  for (const auto &c : contacts) {
    if (c.vertex == 1 && ((c.edge_start == 0 && c.edge_finish == 4) || (c.edge_start2 == 0 && c.edge_finish2 == 4))) {
      has_0_4 = true;
    }
  }
  std::cout << "Did GenerateSilhouetteContacts(centroid) generate edge 0->4 on vertex 1? "
            << (has_0_4 ? "YES" : "NO") << "\n";

  // Check all corners
  for (int i = 0; i < 3; i++) {
    auto c_i = Tube229::GenerateSilhouetteContacts(tri1_f[i], fine_mixes);
    bool has_c = false;
    for (const auto &c : c_i) {
      if (c.vertex == 1 && ((c.edge_start == 0 && c.edge_finish == 4) || (c.edge_start2 == 0 && c.edge_finish2 == 4))) {
        has_c = true;
      }
    }
    std::cout << "Did corner " << i << " generate edge 0->4 on vertex 1? " << (has_c ? "YES" : "NO") << "\n";
  }

  return 0;
}
