#include <iostream>
#include <vector>
#include <string>
#include <cmath>
#include <algorithm>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Annular contacts 0 and 1:
  ContactInfo c0 = MakeContact(3, 2, 2, 1, 800, 2);
  ContactInfo c1 = MakeContact(1, 4, 4, 8, 800, 4);

  std::string err;

  // Let us test various contact 2 choices for u0:
  for (int mix = 0; mix <= 1000; mix += 50) {
    ContactInfo c2_ann = MakeContact(13, 14, 14, 15, mix, 14);
    AxisCertificate ax_ann;
    BigVecQ3 ctr_ann;
    BigRat del_ann;
    ContactInfo cts[3] = {c0, c1, c2_ann};
    if (Tube229::AuditAxis(tri, cts, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000))) {
      BigVecQ3 edges[3] = {Tube229::GetExactEdge(cts[0]), Tube229::GetExactEdge(cts[1]), Tube229::GetExactEdge(cts[2])};
      BigVecQ3 w_coeffs[3] = {BigVecQ3::Cross(edges[1], edges[2]),
                              BigVecQ3::Cross(edges[2], edges[0]),
                              BigVecQ3::Cross(edges[0], edges[1])};
      BigRat w_upper[3];
      for (int m = 0; m < 3; m++) {
        BigRat wm = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
          if (BigRat::Greater(val, wm)) wm = val;
        }
        w_upper[m] = wm;
      }
      BigRat total_defect(0);
      for (int m = 0; m < 3; m++) {
        int sel = cts[m].vertex;
        BigVecQ3 v_sel = Tube229::VertexQ(sel);
        BigRat max_m_defect(0);
        for (int k = 0; k < 20; k++) {
          bool tie = (k == sel) ||
                     (cts[m].mix == 1000 && sel == cts[m].edge_finish && k == cts[m].edge_start) ||
                     (cts[m].mix == 0 && sel == cts[m].edge_start2 && k == cts[m].edge_finish2);
          if (tie) continue;
          BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
          BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta_v);
          BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
          for (int c = 1; c < 3; c++) {
            BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
            if (BigRat::Greater(val, max_s)) max_s = val;
          }
          if (BigRat::Greater(max_s, max_m_defect)) max_m_defect = max_s;
        }
        total_defect = BigRat::Plus(total_defect, BigRat::Times(max_m_defect, w_upper[m]));
      }

      vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
                 ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
                 ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};

      // Best core axis we found earlier:
      // cand: [1->4, 4->8, mix 1000], [10->15, 15->19, mix 400], [10->15, 15->19, mix 0]
      ContactInfo c_core[3] = {
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(10, 15, 15, 19, 400, 15),
        MakeContact(10, 15, 15, 19, 0, 15)
      };
      AxisCertificate ax_c; BigVecQ3 ctr_c; BigRat del_c;
      Tube229::AuditAxis(tri, c_core, &ax_c, &ctr_c, &del_c, &err, BigRat(0));
      vec3 uc = {ctr_c.x.ToDouble() / ax_c.B.ToDouble(),
                 ctr_c.y.ToDouble() / ax_c.B.ToDouble(),
                 ctr_c.z.ToDouble() / ax_c.B.ToDouble()};
      double dot = yocto::dot(yocto::normalize(u0), yocto::normalize(uc));
      double ang = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;

      // Old core axis:
      ContactInfo c_core_old[3] = {
        c0, c1, MakeContact(14, 15, 15, 19, 400, 15)
      };
      Tube229::AuditAxis(tri, c_core_old, &ax_c, &ctr_c, &del_c, &err, BigRat(0));
      vec3 uc_old = {ctr_c.x.ToDouble() / ax_c.B.ToDouble(),
                     ctr_c.y.ToDouble() / ax_c.B.ToDouble(),
                     ctr_c.z.ToDouble() / ax_c.B.ToDouble()};
      double dot_old = yocto::dot(yocto::normalize(u0), yocto::normalize(uc_old));
      double ang_old = std::acos(std::max(-1.0, std::min(1.0, dot_old))) * 180.0 / M_PI;

      std::cout << "mix = " << mix << ": D0 = " << total_defect.ToDouble()
                << ", ang_new = " << ang << " deg, ang_old = " << ang_old << " deg\n";
    }
  }

  return 0;
}
