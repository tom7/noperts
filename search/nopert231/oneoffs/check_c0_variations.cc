#include <iostream>
#include <vector>
#include <iomanip>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  std::cout << "Testing variations around c0 = [150, 1000, 882]:\n";
  for (int m0 = 100; m0 <= 200; m0 += 50) {
    for (int m1 = 900; m1 <= 1000; m1 += 50) {
      for (int m2 = 800; m2 <= 1000; m2 += 20) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(13, 14, 14, 15, m2, 14)
        };
        AxisCertificate ax;
        BigVecQ3 ctr;
        BigRat del;
        std::string err;
        if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
          // Check max defect across all vertices:
          BigRat max_defect(0);
          for (int m_idx = 0; m_idx < 3; m_idx++) {
            int sel = c[m_idx].vertex;
            BigVecQ3 v_sel = Tube229::VertexQ(sel);
            BigVecQ3 edge = Tube229::GetExactEdge(c[m_idx]);
            for (int k = 0; k < 24; k++) {
              bool tie = (k == sel) ||
                         (c[m_idx].mix == 1000 && sel == c[m_idx].edge_finish && k == c[m_idx].edge_start) ||
                         (c[m_idx].mix == 0 && sel == c[m_idx].edge_start2 && k == c[m_idx].edge_finish2);
              if (tie) continue;
              BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
              BigVecQ3 s_coeff = BigVecQ3::Cross(edge, delta_v);
              BigRat max_val = BigVecQ3::Dot(tri.corners[0], s_coeff);
              for (int cr = 1; cr < 3; cr++) {
                BigRat val = BigVecQ3::Dot(tri.corners[cr], s_coeff);
                if (val > max_val) max_val = val;
              }
              BigRat s_upper = max_val + BigRat(6, 1000000000000000LL);
              if (s_upper > max_defect) max_defect = s_upper;
            }
          }
          if (max_defect <= 0) {
            std::cout << "FOUND ZERO DEFECT: [" << m0 << ", " << m1 << ", " << m2 << "]!\n";
          } else if (max_defect < BigRat(1, 10000)) {
            std::cout << "[" << m0 << ", " << m1 << ", " << m2 << "]: max_defect = " << max_defect.ToDouble() << "\n";
          }
        }
      }
    }
  }
  return 0;
}
