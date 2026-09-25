#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  vec3 dir_u0 = {-0.196172, 0.260021, -0.945466};

  vec3 axis = {1, 0, 0};
  vec3 first = yocto::normalize(yocto::cross(dir_u0, axis));
  vec3 second = yocto::cross(dir_u0, first);

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  auto cycle = Tube229::ConvexHull2D(projected);
  std::cout << "Cycle size H = " << cycle.size() << ": ";
  for (int v : cycle) std::cout << v << " ";
  std::cout << "\n";

  return 0;
}
