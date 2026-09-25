#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

static inline vec3 VtoD(const BigVecQ3 &v) {
  return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  ContactInfo c[3] = {
    {2, 1, 2, 1, 1000, 2},
    {4, 8, 4, 8, 1000, 4},
    {19, 3, 19, 3, 1000, 19}
  };

  vec3 tri1_f[3] = {
    VtoD(tri1.corners[0]),
    VtoD(tri1.corners[1]),
    VtoD(tri1.corners[2]),
  };

  for (int m = 0; m < 3; m++) {
    vec3 edge = Tube229::GetDoubleEdge(c[m]);
    int sel = c[m].vertex;
    std::cout << "Contact " << m << " (sel=" << sel << ", edge=" << c[m].edge_start << "->" << c[m].edge_finish << "):\n";
    for (int k = 0; k < 20; k++) {
      if (k == sel) continue;
      if (c[m].mix == 1000 && sel == c[m].edge_finish && k == c[m].edge_start) continue;
      if (c[m].mix == 0 && sel == c[m].edge_start2 && k == c[m].edge_finish2) continue;
      vec3 delta = VtoD(Tube229::VertexQ(k)) - VtoD(Tube229::VertexQ(sel));
      vec3 coeff = yocto::cross(edge, delta);
      double u0 = yocto::dot(tri1_f[0], coeff);
      double u1 = yocto::dot(tri1_f[1], coeff);
      double u2 = yocto::dot(tri1_f[2], coeff);
      double max_u = std::max({u0, u1, u2});
      if (max_u > 0) {
        std::cout << "  FAIL on k=" << k << ": max_u=" << max_u << " (u0=" << u0 << ", u1=" << u1 << ", u2=" << u2 << ")\n";
      }
    }
  }

  // Weight check:
  vec3 c_edges[3] = {Tube229::GetDoubleEdge(c[0]), Tube229::GetDoubleEdge(c[1]), Tube229::GetDoubleEdge(c[2])};
  vec3 weight_coeffs[3] = {
    yocto::cross(c_edges[1], c_edges[2]),
    yocto::cross(c_edges[2], c_edges[0]),
    yocto::cross(c_edges[0], c_edges[1])
  };

  std::cout << "Weights on corners:\n";
  for (int cr = 0; cr < 3; cr++) {
    std::cout << "  Corner " << cr << ": w0=" << yocto::dot(tri1_f[cr], weight_coeffs[0])
              << ", w1=" << yocto::dot(tri1_f[cr], weight_coeffs[1])
              << ", w2=" << yocto::dot(tri1_f[cr], weight_coeffs[2]) << "\n";
  }

  return 0;
}
