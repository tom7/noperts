#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  vec3 tri_f[3] = { ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2]) };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});

  int cands[] = {36, 37, 43, 44, 45, 46, 47, 49, 50, 51, 52};
  for (int ci : cands) {
    const auto &c = contacts[ci];
    std::cout << "Contact " << ci << ": edges (" << c.edge_start << "->" << c.edge_finish
              << ", " << c.edge_start2 << "->" << c.edge_finish2 << "), mix=" << c.mix
              << ", vertex=" << c.vertex << "\n";
  }
  return 0;
}
