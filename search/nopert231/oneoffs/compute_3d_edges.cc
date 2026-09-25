#include <iostream>
#include <vector>
#include <set>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  std::vector<vec3> verts(20);
  for (int i = 0; i < 20; i++) {
    verts[i] = {Tube229::VertexQ(i).x.ToDouble(), Tube229::VertexQ(i).y.ToDouble(), Tube229::VertexQ(i).z.ToDouble()};
  }

  std::set<std::pair<int, int>> edges;
  int num_facets = 0;

  for (int i = 0; i < 20; i++) {
    for (int j = i + 1; j < 20; j++) {
      for (int k = j + 1; k < 20; k++) {
        vec3 normal = yocto::cross(verts[j] - verts[i], verts[k] - verts[i]);
        if (yocto::length(normal) < 1e-12) continue;
        normal = normal / yocto::length(normal);

        int pos = 0, neg = 0;
        for (int m = 0; m < 20; m++) {
          if (m == i || m == j || m == k) continue;
          double d = yocto::dot(verts[m] - verts[i], normal);
          if (d > 1e-9) pos++;
          else if (d < -1e-9) neg++;
        }
        if (pos == 0 || neg == 0) {
          num_facets++;
          auto add_edge = [&](int u, int v) {
            if (u > v) std::swap(u, v);
            edges.insert({u, v});
          };
          add_edge(i, j);
          add_edge(j, k);
          add_edge(i, k);
        }
      }
    }
  }

  std::cout << "3D Convex Hull Facets: " << num_facets << "\n";
  std::cout << "3D Convex Hull Edges: " << edges.size() << "\n";
  std::cout << "Edges list:\n";
  for (const auto &e : edges) {
    std::cout << "  {" << e.first << ", " << e.second << "},\n";
  }

  return 0;
}
