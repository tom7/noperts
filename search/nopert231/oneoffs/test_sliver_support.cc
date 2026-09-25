#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  // The sliver T^- has corners:
  // c2 (Corner 2 of tri1)
  // and the two seam intersection points with edges (0->2) and (1->2).
  // On the whole tri1:
  // Edge 2->1: v2, v1
  // Edge 1->4: v1, v4
  // Edge 10->15: v10, v15
  int e_s[3] = {2, 1, 10};
  int e_f[3] = {1, 4, 15};
  int sel[3] = {2, 4, 10};

  for (int m = 0; m < 3; m++) {
    ContactInfo c = {e_s[m], e_f[m], e_s[m], e_f[m], 1000, sel[m]};
    vec3 edge = Tube229::GetDoubleEdge(c);
    double max_err_c2 = -1e9;
    double max_err_tri1 = -1e9;
    for (int k = 0; k < 20; k++) {
      if (k == sel[m] || k == e_s[m] || k == e_f[m]) continue;
      vec3 delta = {Tube229::VertexQ(k).x.ToDouble() - Tube229::VertexQ(sel[m]).x.ToDouble(),
                    Tube229::VertexQ(k).y.ToDouble() - Tube229::VertexQ(sel[m]).y.ToDouble(),
                    Tube229::VertexQ(k).z.ToDouble() - Tube229::VertexQ(sel[m]).z.ToDouble()};
      vec3 coeff = yocto::cross(edge, delta);
      // check Corner 2
      vec3 c2 = {tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()};
      double err_c2 = yocto::dot(c2, coeff);
      if (err_c2 > max_err_c2) max_err_c2 = err_c2;
      // check all 3 corners of tri1
      for (int cn = 0; cn < 3; cn++) {
        vec3 c_cn = {tri1.corners[cn].x.ToDouble(), tri1.corners[cn].y.ToDouble(), tri1.corners[cn].z.ToDouble()};
        double err = yocto::dot(c_cn, coeff);
        if (err > max_err_tri1) max_err_tri1 = err;
      }
    }
    std::cout << "Edge " << e_s[m] << "->" << e_f[m] << " (sel=" << sel[m] << "):\n"
              << "  max_err at Corner 2: " << max_err_c2 << "\n"
              << "  max_err across tri1: " << max_err_tri1 << "\n";
  }

  return 0;
}
