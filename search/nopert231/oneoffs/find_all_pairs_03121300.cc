#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 Vert(int k) {
  BigVecQ3 v = Tube229::VertexQ(k);
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 tri_f[3] = {
    vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()},
    vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()},
    vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()}
  };

  int valid_pairs = 0;
  for (int v = 0; v < 22; v++) {
    for (int u = 0; u < 22; u++) {
      if (u == v) continue;
      for (int w = 0; w < 22; w++) {
        if (w == v || w == u) continue;

        for (int mix : {0, 100, 200, 333, 500, 666, 800, 900, 1000}) {
          ContactInfo c;
          c.vertex = v;
          c.edge_start = u; c.edge_finish = v;
          c.edge_start2 = v; c.edge_finish2 = w;
          c.mix = mix;

          vec3 edge = Tube229::GetDoubleEdge(c);
          bool ok = true;
          for (int k = 0; k < 22; k++) {
            bool tie = (k == v) ||
                       (mix == 1000 && v == c.edge_finish && k == c.edge_start) ||
                       (mix == 0 && v == c.edge_start2 && k == c.edge_finish2);
            if (tie) continue;
            vec3 delta_v = Vert(k) - Vert(v);
            vec3 coeff = yocto::cross(edge, delta_v);
            double u0 = yocto::dot(tri_f[0], coeff);
            double u1 = yocto::dot(tri_f[1], coeff);
            double u2 = yocto::dot(tri_f[2], coeff);
            if (std::max({u0, u1, u2}) > 1e-12) {
              ok = false;
              break;
            }
          }
          if (ok) {
            std::cout << "Valid contact: v=" << v << " (" << u << "->" << v << ", " << v << "->" << w << ") mix=" << mix << "\n";
            valid_pairs++;
          }
        }
      }
    }
  }

  std::cout << "Total valid contacts on 03121300: " << valid_pairs << "\n";
  return 0;
}
