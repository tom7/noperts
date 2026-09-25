#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include "bignum/big-overloads.h"
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  // Test contacts of annular axis (axis 0 of base_sib)
  ContactInfo annular_contacts[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  // Complementary axes contacts (axes 1, 2, 3 of base_sib)
  ContactInfo comp_contacts[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };

  std::string canyon_path = "031213002112122012121";

  std::cout << "Depth |   Diam   | Inner B | Annular B | Defect D   | Comp Delta | Dominance?\n";
  std::cout << "------+----------+---------+-----------+------------+------------+-----------\n";

  for (int len = 21; len >= 7; len--) {
    std::string p = canyon_path.substr(0, len);
    TriangleQ tri = TriangleFromPath(p);

    // 1. Diameter
    vec3 c0 = ToDouble(tri.corners[0]);
    vec3 c1 = ToDouble(tri.corners[1]);
    vec3 c2 = ToDouble(tri.corners[2]);
    double diam = std::max({yocto::length(c0 - c1), yocto::length(c1 - c2), yocto::length(c2 - c0)});

    // 2. Inner core axis
    AxisCertificate inner_core;
    BigVecQ3 inner_center;
    BigRat inner_delta;
    std::string inner_fail;
    bool inner_ok = Tube229::FindHullSupportAxis(tri, &inner_core, &inner_center, &inner_delta, &inner_fail);

    // 3. Annular axis: compute w_coeffs, w_upper, and defect D
    BigVecQ3 edges[3] = {
      Tube229::GetExactEdge(annular_contacts[0]),
      Tube229::GetExactEdge(annular_contacts[1]),
      Tube229::GetExactEdge(annular_contacts[2])
    };
    BigVecQ3 coeff0 = BigVecQ3::Cross(edges[1], edges[2]);
    BigVecQ3 coeff1 = BigVecQ3::Cross(edges[2], edges[0]);
    BigVecQ3 coeff2 = BigVecQ3::Cross(edges[0], edges[1]);
    BigVecQ3 w_coeffs[3] = {coeff0, coeff1, coeff2};

    BigRat w_upper[3];
    BigRat sum_w_upper(0);
    bool w_ok = true;
    for (int m = 0; m < 3; m++) {
      BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs[m]);
      for (int c = 1; c < 3; c++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs[m]);
        if (val > w_max) w_max = val;
      }
      w_upper[m] = w_max;
      sum_w_upper = sum_w_upper + w_max;
    }
    BigRat annular_B = sum_w_upper * BigRat(2);

    // Defect on annular contacts:
    BigRat total_defect(0);
    for (int m = 0; m < 3; m++) {
      int sel = annular_contacts[m].vertex;
      BigVecQ3 v_sel = Tube229::VertexQ(sel);
      BigRat max_m_defect(0);
      for (int k = 0; k < 20; k++) {
        bool tie = (k == sel) ||
                   (annular_contacts[m].mix == 1000 && sel == annular_contacts[m].edge_finish && k == annular_contacts[m].edge_start) ||
                   (annular_contacts[m].mix == 0 && sel == annular_contacts[m].edge_start2 && k == annular_contacts[m].edge_finish2);
        if (tie) continue;
        BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
        BigVecQ3 s_coeff = BigVecQ3::Cross(edges[m], delta_v);
        BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
        for (int c = 1; c < 3; c++) {
          BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
          if (val > max_s) max_s = val;
        }
        if (max_s > max_m_defect) max_m_defect = max_s;
      }
      total_defect = total_defect + max_m_defect * w_upper[m];
    }

    // 4. Complementary delta
    BigRat max_comp_delta{0};
    for (int a = 0; a < 3; a++) {
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      std::string fail;
      if (Tube229::AuditAxis(tri, comp_contacts[a], &cert, &center, &delta, &fail)) {
        if (delta > max_comp_delta) max_comp_delta = delta;
      }
    }

    // 5. Test annular dominance with candidate r_min, r
    // Try multiple candidate radii
    bool dom_ok = false;
    BigRat best_r_min, best_r;
    for (int r_denom : {2000, 1000, 500, 200, 100}) {
      for (int r_min_denom : {20000, 10000, 5000, 2000, 1000}) {
        if (r_min_denom <= r_denom) continue;
        BigRat cand_r_min(1, r_min_denom);
        BigRat cand_r(1, r_denom);
        BigRat c_cone(1, 10);
        if (Tube229::CheckAnnularDominance(annular_B, total_defect, c_cone, max_comp_delta, &cand_r_min, &cand_r)) {
          dom_ok = true;
          best_r_min = cand_r_min;
          best_r = cand_r;
          break;
        }
      }
      if (dom_ok) break;
    }

    std::cout << std::setw(5) << len << " | "
              << std::scientific << std::setprecision(2) << diam << " | "
              << (inner_ok ? "OK" : "FAIL") << " | "
              << std::setprecision(3) << annular_B.ToDouble() << " | "
              << std::scientific << std::setprecision(2) << total_defect.ToDouble() << " | "
              << std::setprecision(2) << max_comp_delta.ToDouble() << " | "
              << (dom_ok ? ("YES (r=" + best_r.ToString() + ", r_min=" + best_r_min.ToString() + ")") : "NO") << "\n";
  }

  return 0;
}
