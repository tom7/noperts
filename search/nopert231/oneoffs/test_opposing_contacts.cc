#include <iostream>
#include <vector>
#include <iomanip>

#include "ruperts/tubetree229.h"
#include "ruperts/nopert231.h"
#include "ruperts/tube229.h"

using namespace tubetree229;
using vec2 = Tube229::vec2;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 u = yocto::normalize(vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()});

  vec3 axis = vec3{0, 1, 0};
  vec3 first = yocto::normalize(yocto::cross(u, axis));
  vec3 second = yocto::cross(u, first);

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> hull = Tube229::ConvexHull2D(projected);
  int H = hull.size();

  // The separating normal that was found earlier
  vec3 sep_norm = yocto::normalize(vec3{-5.32008e-07, 6.40865e-07, 1.0327e-06});

  std::cout << "Testing ALL possible single contact torques against separating normal at Corner 2:\n";
  std::cout << "Separating normal: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";

  for (int pos = 0; pos < H; pos++) {
    int v = hull[pos];
    int prev = hull[(pos - 1 + H) % H];
    int next = hull[(pos + 1) % H];

    // Sample normal cone at vertex v
    for (int mix = 0; mix <= 1000; mix += 100) {
      ContactInfo ci;
      ci.vertex = v;
      ci.edge_start = prev;
      ci.edge_finish = v;
      ci.edge_start2 = v;
      ci.edge_finish2 = next;
      ci.mix = mix;

      vec3 edge = Tube229::GetDoubleEdge(ci);
      vec3 lift = yocto::cross(u, edge);
      vec3 tau = yocto::cross(Vertex(v), lift);

      // In projection, the 2D normal is:
      vec2 n2 = vec2{yocto::dot(lift, first), yocto::dot(lift, second)};
      double dot_sep = yocto::dot(tau, -sep_norm);

      // We want to know if there's any tau that opposes sep_norm (dot_sep > 0)
      if (dot_sep > 0) {
        std::cout << "  Vertex " << v << " mix=" << mix
                  << " has POSITIVE opposing torque: " << dot_sep
                  << " with 2D normal: (" << n2.x << ", " << n2.y << ")\n";
      }
    }
  }

  return 0;
}
