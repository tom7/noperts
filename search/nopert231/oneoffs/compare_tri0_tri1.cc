#include <iostream>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri0 = TriangleFromPath("031213002112122012120");
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  std::cout << "tri0 corners:\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  [" << i << "] = (" << tri0.corners[i].x.ToDouble()
              << ", " << tri0.corners[i].y.ToDouble()
              << ", " << tri0.corners[i].z.ToDouble() << ")\n";
  }
  std::cout << "tri1 corners:\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "  [" << i << "] = (" << tri1.corners[i].x.ToDouble()
              << ", " << tri1.corners[i].y.ToDouble()
              << ", " << tri1.corners[i].z.ToDouble() << ")\n";
  }

  // How far apart are the centroids?
  vec3 c0 = {
    (tri0.corners[0].x.ToDouble() + tri0.corners[1].x.ToDouble() + tri0.corners[2].x.ToDouble()) / 3.0,
    (tri0.corners[0].y.ToDouble() + tri0.corners[1].y.ToDouble() + tri0.corners[2].y.ToDouble()) / 3.0,
    (tri0.corners[0].z.ToDouble() + tri0.corners[1].z.ToDouble() + tri0.corners[2].z.ToDouble()) / 3.0
  };
  vec3 c1 = {
    (tri1.corners[0].x.ToDouble() + tri1.corners[1].x.ToDouble() + tri1.corners[2].x.ToDouble()) / 3.0,
    (tri1.corners[0].y.ToDouble() + tri1.corners[1].y.ToDouble() + tri1.corners[2].y.ToDouble()) / 3.0,
    (tri1.corners[0].z.ToDouble() + tri1.corners[1].z.ToDouble() + tri1.corners[2].z.ToDouble()) / 3.0
  };
  std::cout << "Distance between centroids: " << yocto::length(c1 - c0) << "\n";

  return 0;
}
