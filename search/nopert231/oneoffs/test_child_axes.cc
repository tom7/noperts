#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string parent = "03121303200";
  for (int child = 0; child < 4; child++) {
    std::string path = parent + std::to_string(child);
    TriangleQ tri = TriangleFromPath(path);
    std::cout << "\n================ Child " << path << " ================\n";

    ContactInfo c0[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(13, 14, 14, 15, 200, 14)
    };
    AxisCertificate ax0;
    BigVecQ3 center0;
    BigRat delta0;
    std::string err;
    if (Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000))) {
      std::cout << "Axis 0 B=" << ax0.B.ToDouble() << " delta=" << delta0.ToDouble() << "\n";
      // Compute D0 on this child:
      BigRat D0(0);
      BigVecQ3 edges0[3] = {Tube229::GetExactEdge(c0[0]), Tube229::GetExactEdge(c0[1]), Tube229::GetExactEdge(c0[2])};
      BigRat w_upper0[3];
      for (int m = 0; m < 3; m++) {
        BigVecQ3 coeff = BigVecQ3::Cross(edges0[(m + 1) % 3], edges0[(m + 2) % 3]);
        BigRat w_max = BigVecQ3::Dot(tri.corners[0], coeff);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], coeff);
          if (val > w_max) w_max = val;
        }
        w_upper0[m] = w_max + BigRat(6, 1000000000000000LL);
      }
      for (int m = 0; m < 3; m++) {
        int sel = c0[m].vertex;
        BigVecQ3 v_sel = Tube229::VertexQ(sel);
        BigRat max_m_defect(0);
        for (int k = 0; k < 20; k++) {
          if (k == sel) continue;
          BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
          BigVecQ3 s_coeff = BigVecQ3::Cross(edges0[m], delta_v);
          BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
          for (int c = 1; c < 3; c++) {
            BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
            if (val > max_s) max_s = val;
          }
          if (max_s > max_m_defect) max_m_defect = max_s;
        }
        D0 = D0 + max_m_defect * w_upper0[m];
      }
      std::cout << "Child " << path << " D0 = " << D0.ToDouble() << "\n";

    } else {
      std::cout << "Axis 0 audit failed: " << err << "\n";
    }
  }
  return 0;
}
