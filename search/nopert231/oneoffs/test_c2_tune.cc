#include <iostream>
#include <vector>
#include <cmath>
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

  ContactInfo c0 = MakeContact(3, 2, 2, 1, 800, 2);
  ContactInfo c1 = MakeContact(1, 4, 4, 8, 800, 4);

  // Core axis: mix 400 on (14->15, 15->19)
  ContactInfo c_core[3] = {c0, c1, MakeContact(14, 15, 15, 19, 400, 15)};
  AxisCertificate ax_core; BigVecQ3 ctr_core; BigRat del_core;
  std::string err;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  vec3 uc = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
             ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
             ctr_core.z.ToDouble() / ax_core.B.ToDouble()};

  std::cout << "Testing u0 with contact 2 on (14->15, 15->19):\n";
  for (int mix = 0; mix <= 1000; mix += 50) {
    ContactInfo c_ann[3] = {c0, c1, MakeContact(14, 15, 15, 19, mix, 15)};
    AxisCertificate ax_ann; BigVecQ3 ctr_ann; BigRat del_ann;
    if (Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000))) {
      BigVecQ3 edges[3] = {Tube229::GetExactEdge(c_ann[0]), Tube229::GetExactEdge(c_ann[1]), Tube229::GetExactEdge(c_ann[2])};
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
        int sel = c_ann[m].vertex;
        BigVecQ3 v_sel = Tube229::VertexQ(sel);
        BigRat max_m_defect(0);
        for (int k = 0; k < 20; k++) {
          bool tie = (k == sel) ||
                     (c_ann[m].mix == 1000 && sel == c_ann[m].edge_finish && k == c_ann[m].edge_start) ||
                     (c_ann[m].mix == 0 && sel == c_ann[m].edge_start2 && k == c_ann[m].edge_finish2);
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
      double dot = yocto::dot(yocto::normalize(u0), yocto::normalize(uc));
      double ang = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;

      std::cout << "mix = " << mix << ": D0 = " << total_defect.ToDouble()
                << ", angle to u_core = " << ang << " deg, ||u0|| = " << yocto::length(u0) << "\n";
    }
  }
  return 0;
}
