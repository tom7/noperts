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

  // Test edge (10 -> 15) with vertex 10 and vertex 15
  vec3 v10 = {Tube229::VertexQ(10).x.ToDouble(), Tube229::VertexQ(10).y.ToDouble(), Tube229::VertexQ(10).z.ToDouble()};
  vec3 v15 = {Tube229::VertexQ(15).x.ToDouble(), Tube229::VertexQ(15).y.ToDouble(), Tube229::VertexQ(15).z.ToDouble()};
  vec3 edge_10_15 = v15 - v10;

  std::cout << "Testing support of edge (10 -> 15) with vertex 10 across tri1:\n";
  for (int k = 0; k < 20; k++) {
    if (k == 10 || k == 15) continue;
    vec3 vk = {Tube229::VertexQ(k).x.ToDouble(), Tube229::VertexQ(k).y.ToDouble(), Tube229::VertexQ(k).z.ToDouble()};
    vec3 delta = vk - v10;
    vec3 coeff = yocto::cross(edge_10_15, delta);
    for (int c = 0; c < 3; c++) {
      double dot = yocto::dot(tri1_f[c], coeff);
      if (dot > 0) {
        std::cout << "  Corner " << c << " FAILS on vertex " << k << " (dot = " << dot << ")\n";
      }
    }
  }

  std::cout << "\nTesting support of edge (10 -> 15) with vertex 15 across tri1:\n";
  for (int k = 0; k < 20; k++) {
    if (k == 10 || k == 15) continue;
    vec3 vk = {Tube229::VertexQ(k).x.ToDouble(), Tube229::VertexQ(k).y.ToDouble(), Tube229::VertexQ(k).z.ToDouble()};
    vec3 delta = vk - v15;
    vec3 coeff = yocto::cross(edge_10_15, delta);
    for (int c = 0; c < 3; c++) {
      double dot = yocto::dot(tri1_f[c], coeff);
      if (dot > 0) {
        std::cout << "  Corner " << c << " FAILS on vertex " << k << " (dot = " << dot << ")\n";
      }
    }
  }

  return 0;
}
