#include <iostream>
#include <iomanip>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  ContactInfo c[3] = {
    {2, 3, 2, 3, 2, 1000},
    {4, 4, 8, 4, 8, 1000},
    {15, 15, 19, 15, 19, 1000}
  };

  vec3 tri1_f[3] = {
    ToDouble(tri1.corners[0]),
    ToDouble(tri1.corners[1]),
    ToDouble(tri1.corners[2]),
  };

  std::cout << std::setprecision(12);
  for (int m = 0; m < 3; m++) {
    vec3 edge = Tube229::GetDoubleEdge(c[m]);
    int sel = c[m].vertex;
    std::cout << "Contact " << m << " (sel=" << sel << "):\n";
    for (int k = 0; k < Tube229::NUM_VERTICES; k++) {
      if (k == sel) continue;
      if (k == c[m].edge_start && sel == c[m].edge_finish) continue;
      vec3 delta = Tube229::Vertex(k) - Tube229::Vertex(sel);
      vec3 coeff = yocto::cross(edge, delta);
      double u0 = yocto::dot(tri1_f[0], coeff);
      double u1 = yocto::dot(tri1_f[1], coeff);
      double u2 = yocto::dot(tri1_f[2], coeff);
      double max_u = std::max({u0, u1, u2});
      if (max_u > -1e-6) {
        std::cout << "  k=" << std::setw(2) << k << ": max_u=" << std::setw(16) << max_u
                  << " (u0=" << u0 << ", u1=" << u1 << ", u2=" << u2 << ")\n";
      }
    }
  }

  Tube229::CandidateTriple cand;
  bool ok = Tube229::DoubleCheckAxis(tri1, c, &cand);
  std::cout << "DoubleCheckAxis on tri1: " << (ok ? "PASS" : "FAIL") << "\n";
  return 0;
}
