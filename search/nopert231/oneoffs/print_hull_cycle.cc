#include <iostream>
#include <vector>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "geom/hull-2d.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  using vec2 = Hull2D::vec2;
  vec3 up = {0, 0, 1};

  for (int c = 0; c < 3; c++) {
    vec3 corner = {tri1.corners[c].x.ToDouble(), tri1.corners[c].y.ToDouble(), tri1.corners[c].z.ToDouble()};
    corner = corner / yocto::length(corner);
    vec3 first_c = yocto::normalize(yocto::cross(up, corner));
    vec3 second_c = yocto::cross(corner, first_c);
    std::vector<vec2> proj(20);
    for (int k = 0; k < 20; k++) {
      vec3 vk = {Tube229::VertexQ(k).x.ToDouble(), Tube229::VertexQ(k).y.ToDouble(), Tube229::VertexQ(k).z.ToDouble()};
      proj[k] = vec2{yocto::dot(vk, first_c), yocto::dot(vk, second_c)};
    }
    std::vector<int> cyc = Hull2D::GrahamScan(proj);
    std::cout << "\nCorner " << c << " Convex Hull Cycle (size=" << cyc.size() << "):\n";
    for (size_t i = 0; i < cyc.size(); i++) {
      std::cout << "  pos " << i << ": vertex " << cyc[i] << "\n";
    }
  }

  return 0;
}
