#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  BigVecQ3 edges[3] = {Tube229::GetExactEdge(c[0]), Tube229::GetExactEdge(c[1]), Tube229::GetExactEdge(c[2])};
  BigRat support_error(6, 1000000000000000LL);

  for (int m = 0; m < 3; m++) {
    int sel = c[m].vertex;
    BigVecQ3 v_sel = VertexQ(sel);
    BigRat max_s_all(-1000000);
    int worst_k = -1;
    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (c[m].mix == 1000 && sel == c[m].edge_finish && k == c[m].edge_start) ||
                 (c[m].mix == 0 && sel == c[m].edge_start2 && k == c[m].edge_finish2);
      if (tie) continue;
      BigVecQ3 v_k = VertexQ(k);
      BigVecQ3 delta = v_k - v_sel;
      BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta);
      BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
      for (int c_idx = 1; c_idx < 3; c_idx++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c_idx], s_coeff);
        if (val > max_s) max_s = val;
      }
      BigRat s_upper = max_s + support_error;
      if (s_upper > max_s_all) {
        max_s_all = s_upper;
        worst_k = k;
      }
    }
    std::cout << "Contact " << m << " (vertex " << sel << "): max supportUpper = "
              << max_s_all.ToString() << " (" << max_s_all.ToDouble() << "), worst k = " << worst_k << "\n";
  }
  return 0;
}
