#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo contacts[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };

  BigVecQ3 edges[3];
  for (int i = 0; i < 3; i++) {
    BigVecQ3 e1 = VertexQ(contacts[i].edge_finish) - VertexQ(contacts[i].edge_start);
    BigVecQ3 e2 = VertexQ(contacts[i].edge_finish2) - VertexQ(contacts[i].edge_start2);
    BigRat alpha(contacts[i].mix, 1000);
    edges[i] = {alpha * e1.x + (BigRat(1) - alpha) * e2.x,
                alpha * e1.y + (BigRat(1) - alpha) * e2.y,
                alpha * e1.z + (BigRat(1) - alpha) * e2.z};
  }

  BigRat support_error(1, 100000000);
  for (int m = 0; m < 3; m++) {
    int sel = contacts[m].vertex;
    BigVecQ3 v_sel = VertexQ(sel);
    for (int k = 0; k < NUM_VERTICES; k++) {
      bool tie = (k == sel) ||
                 (contacts[m].mix == 1000 && sel == contacts[m].edge_finish && k == contacts[m].edge_start) ||
                 (contacts[m].mix == 0 && sel == contacts[m].edge_start2 && k == contacts[m].edge_finish2);
      if (tie) continue;
      BigVecQ3 v_k = VertexQ(k);
      BigVecQ3 delta = v_k - v_sel;
      BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta);
      BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
      for (int c = 1; c < 3; c++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
        if (val > max_s) max_s = val;
      }
      BigRat s_upper = max_s + support_error;
      if (s_upper > 0) {
        std::cout << "m=" << m << " (sel=" << sel << "), vertex k=" << k
                  << ": s_upper = " << s_upper.ToDouble() << "\n";
      }
    }
  }
  return 0;
}
