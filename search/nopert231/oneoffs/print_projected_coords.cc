#include <iostream>
#include <vector>
#include <iomanip>
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
  vec3 u = centroid / yocto::length(centroid);

  vec3 up = {0, 0, 1};
  if (std::abs(yocto::dot(u, up)) > 0.99) up = {0, 1, 0};
  vec3 e1 = yocto::normalize(yocto::cross(up, u));
  vec3 e2 = yocto::cross(u, e1);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "View vector u: (" << u.x << ", " << u.y << ", " << u.z << ")\n";
  std::cout << "Projected coordinates of 20 vertices:\n";
  for (int k = 0; k < 20; k++) {
    vec3 vk = {Tube229::VertexQ(k).x.ToDouble(), Tube229::VertexQ(k).y.ToDouble(), Tube229::VertexQ(k).z.ToDouble()};
    double px = yocto::dot(vk, e1);
    double py = yocto::dot(vk, e2);
    std::cout << "  v" << std::setw(2) << k << ": (" << std::setw(9) << px << ", " << std::setw(9) << py << ")\n";
  }

  return 0;
}
