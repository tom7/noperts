#include <iostream>
#include <vector>
#include <iomanip>
#include <cmath>

#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;
using vec2 = Tube229::vec2;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 tri_f[3] = {
    vec3{tri.corners[0].x.ToDouble(), tri.corners[0].y.ToDouble(), tri.corners[0].z.ToDouble()},
    vec3{tri.corners[1].x.ToDouble(), tri.corners[1].y.ToDouble(), tri.corners[1].z.ToDouble()},
    vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()}
  };
  vec3 u2 = yocto::normalize(tri_f[2]);
  vec3 omega = yocto::normalize(vec3{-0.400992, 0.483041, 0.778381});
  vec3 w = -omega;

  // Contact 0: edge (3 -> 2), vertex 2
  // Contact 1: edge (4 -> 8), vertex 4
  // Contact 2: edge (15 -> 19), vertex 15
  ContactInfo contacts[3] = {
    {2, 3, 2, 3, 2, 1000},
    {4, 4, 8, 4, 8, 1000},
    {15, 15, 19, 15, 19, 1000}
  };

  Tube229::CandidateTriple cand;
  bool ok = Tube229::DoubleCheckAxis(tri, contacts, &cand);
  std::cout << "DoubleCheckAxis ok = " << (ok ? "YES" : "NO") << "\n";
  if (ok) {
    double dot_w = yocto::dot(cand.normalized_a, w);
    std::cout << "norm_a = (" << cand.normalized_a.x << ", "
              << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
    std::cout << "dot(normalized_a, -omega) = " << dot_w << "\n";
  }

  // Let's also check all combinations of hull edges and vertices
  std::vector<int> hull = {19, 3, 2, 1, 4, 8, 9, 10, 15};
  int H = hull.size();

  double best_dot = -1.0;
  ContactInfo best_c[3];

  for (int i0 = 0; i0 < H; i0++) {
    int v0_a = hull[i0], v0_b = hull[(i0+1)%H];
    for (int sel0 : {v0_a, v0_b}) {
      for (int i1 = i0 + 1; i1 < H; i1++) {
        int v1_a = hull[i1], v1_b = hull[(i1+1)%H];
        for (int sel1 : {v1_a, v1_b}) {
          for (int i2 = i1 + 1; i2 < H; i2++) {
            int v2_a = hull[i2], v2_b = hull[(i2+1)%H];
            for (int sel2 : {v2_a, v2_b}) {
              ContactInfo c[3] = {
                {sel0, v0_a, v0_b, v0_a, v0_b, 1000},
                {sel1, v1_a, v1_b, v1_a, v1_b, 1000},
                {sel2, v2_a, v2_b, v2_a, v2_b, 1000}
              };
              Tube229::CandidateTriple cd;
              if (Tube229::DoubleCheckAxis(tri, c, &cd)) {
                double dw = yocto::dot(cd.normalized_a, w);
                if (dw > best_dot) {
                  best_dot = dw;
                  for (int m = 0; m < 3; m++) best_c[m] = c[m];
                }
              }
            }
          }
        }
      }
    }
  }

  std::cout << "\nBest dot(normalized_a, -omega) over all 3-contact combinations: " << best_dot << "\n";
  if (best_dot > -1.0) {
    for (int m = 0; m < 3; m++) {
      std::cout << "  Contact " << m << ": v=" << best_c[m].vertex
                << " edge=(" << best_c[m].edge_start << "->" << best_c[m].edge_finish << ")\n";
    }
  }

  return 0;
}
