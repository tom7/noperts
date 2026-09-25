#include <iostream>
#include <iomanip>

#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 c2 = vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()};
  vec3 u = yocto::normalize(c2);

  std::cout << "Path: " << path << " Corner 2:\n";
  std::cout << "  Rational: (" << tri.corners[2].x.ToString() << ", "
            << tri.corners[2].y.ToString() << ", "
            << tri.corners[2].z.ToString() << ")\n";
  std::cout << "  Unit view: (" << std::fixed << std::setprecision(8)
            << u.x << ", " << u.y << ", " << u.z << ")\n";

  // Check 2D projected hull at Corner 2
  vec3 axis = vec3{0, 1, 0};
  vec3 first = yocto::normalize(yocto::cross(u, axis));
  vec3 second = yocto::cross(u, first);

  std::cout << "\nAll 20 vertices projected at Corner 2:\n";
  for (int v = 0; v < NUM_VERTICES; v++) {
    double px = yocto::dot(Vertex(v), first);
    double py = yocto::dot(Vertex(v), second);
    std::cout << "  v" << std::setw(2) << v << ": ("
              << std::setw(11) << px << ", "
              << std::setw(11) << py << ")\n";
  }

  return 0;
}
