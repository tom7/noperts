#include <iostream>
#include <vector>
#include <cmath>
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

static bool Bary4(const BigVecQ3 pts[4], const BigVecQ3 &target, BigRat lam[4]) {
  BigVecQ3 v0 = pts[0] - pts[3];
  BigVecQ3 v1 = pts[1] - pts[3];
  BigVecQ3 v2 = pts[2] - pts[3];
  BigVecQ3 w = target - pts[3];
  BigRat den = BigVecQ3::Det(v0, v1, v2);
  if (den == 0) return false;
  lam[0] = BigVecQ3::Det(w, v1, v2) / den;
  lam[1] = BigVecQ3::Det(v0, w, v2) / den;
  lam[2] = BigVecQ3::Det(v0, v1, w) / den;
  lam[3] = BigRat(1) - lam[0] - lam[1] - lam[2];
  return true;
}

int main() {
  std::vector<std::string> leaves = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  // Contacts from test_all_canyon_leaves.cc
  ContactInfo contacts[4][3] = {
    // Axis 0 (annular, with v14)
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14)},
    // Axis 1 (zero-defect complement)
    {MakeContact(15, 19, 19, 3, 200, 19), MakeContact(2, 1, 1, 4, 200, 1), MakeContact(8, 9, 9, 10, 200, 9)},
    // Axis 2 (zero-defect complement)
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15)},
    // Axis 3 (zero-defect complement)
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(10, 15, 15, 19, 800, 15)}
  };

  // Zero-defect core axis from find_closest_core_axis
  ContactInfo core_contacts[3] = {
    MakeContact(5, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15),
    MakeContact(7, 2, 2, 5, 600, 2)
  };

  for (size_t leaf_idx = 0; leaf_idx < leaves.size(); leaf_idx++) {
    const auto &path = leaves[leaf_idx];
    std::cout << "\n============================================\n";
    std::cout << "Node " << path << " (depth " << path.size() - 1 << ")\n";
    TriangleQ tri = TriangleFromPath(path);

    BigVecQ3 centers[4];
    BigRat deltas[4];
    AxisCertificate axes[4];
    for (int a = 0; a < 4; a++) {
      std::string err;
      BigRat max_def = (a == 0) ? BigRat(5, 1000) : BigRat(0);
      Tube229::AuditAxis(tri, contacts[a], &axes[a], &centers[a], &deltas[a], &err, max_def);
    }

    BigVecQ3 core_center;
    BigRat core_delta;
    AxisCertificate core_axis;
    std::string core_err;
    Tube229::AuditAxis(tri, core_contacts, &core_axis, &core_center, &core_delta, &core_err, BigRat(0));

    // Compute D0
    BigVecQ3 edges0[3] = {
      Tube229::GetExactEdge(contacts[0][0]),
      Tube229::GetExactEdge(contacts[0][1]),
      Tube229::GetExactEdge(contacts[0][2])
    };
    BigVecQ3 w_coeffs0[3] = {
      BigVecQ3::Cross(edges0[1], edges0[2]),
      BigVecQ3::Cross(edges0[2], edges0[0]),
      BigVecQ3::Cross(edges0[0], edges0[1])
    };
    BigRat w_upper0[3];
    for (int m = 0; m < 3; m++) {
      BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs0[m]);
      for (int c = 1; c < 3; c++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs0[m]);
        if (val > w_max) w_max = val;
      }
      w_upper0[m] = w_max;
    }
    BigRat D0(0);
    for (int m = 0; m < 3; m++) {
      int sel = contacts[0][m].vertex;
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

    std::cout << "  delta0 = " << deltas[0].ToDouble() << " D0 = " << D0.ToDouble()
              << " B0 = " << axes[0].B.ToDouble() << "\n";
    std::cout << "  core_B = " << core_axis.B.ToDouble() << " core_delta = " << core_delta.ToDouble() << "\n";

    // Decomposition: core_center = lam * center0 + w
    BigVecQ3 u = centers[0];
    BigVecQ3 v = core_center;
    BigRat u_sq = BigVecQ3::Dot(u, u);
    BigRat v_sq = BigVecQ3::Dot(v, v);
    BigRat uv = BigVecQ3::Dot(u, v);
    BigRat lam = uv / u_sq;
    BigRat w_sq = v_sq - lam * lam * u_sq;
    double u_len = std::sqrt(u_sq.ToDouble());
    double v_len = std::sqrt(v_sq.ToDouble());
    double cos_uv = uv.ToDouble() / (u_len * v_len);
    double angle_deg = std::acos(std::max(-1.0, std::min(1.0, cos_uv))) * 180.0 / M_PI;
    std::cout << "  u_len = " << u_len << " v_len = " << v_len
              << " angle = " << angle_deg << " deg, lam = " << lam.ToDouble() << "\n";

    // Now test if there exists a valid parameter set (c_cone, c_core, c_comp, r, r_min)
    BigRat delta_max = deltas[0];
    for (int a = 1; a < 4; a++) if (deltas[a] > delta_max) delta_max = deltas[a];

    bool found = false;
    for (int cc_i = 1; cc_i <= 100; cc_i++) {
      BigRat c_cone(cc_i, 1000); // 0.001 to 0.100
      if (c_cone <= deltas[0]) continue;
      if (c_cone * c_cone >= u_sq) continue;

      // Check barycentric validity of (v0, u1, u2, u3)
      BigVecQ3 dec_pts[4];
      BigRat scale_0 = (deltas[0] + BigRat(1, 100000)) / c_cone; // test with c_comp = 1e-5
      // Actually test Lean's exact octahedron targets
      dec_pts[0] = centers[0] * (scale_0);
      dec_pts[1] = centers[1];
      dec_pts[2] = centers[2];
      dec_pts[3] = centers[3];

      BigVecQ3 oct_targets[6] = {
        BigVecQ3(BigRat(1), BigRat(0), BigRat(0)),
        BigVecQ3(BigRat(-1), BigRat(0), BigRat(0)),
        BigVecQ3(BigRat(0), BigRat(1), BigRat(0)),
        BigVecQ3(BigRat(0), BigRat(-1), BigRat(0)),
        BigVecQ3(BigRat(0), BigRat(0), BigRat(1)),
        BigVecQ3(BigRat(0), BigRat(0), BigRat(-1))
      };
      BigRat c_comp_test = deltas[0] + BigRat(1, 100000); // c_comp >= delta
      BigRat R_target = (c_comp_test + deltas[0]) * BigRat(7, 4);

      bool bary_ok = true;
      for (int k = 0; k < 6; k++) {
        BigVecQ3 tgt = oct_targets[k] * R_target;
        BigRat bary_lam[4];
        if (!Bary4(dec_pts, tgt, bary_lam) || bary_lam[0] < 0 || bary_lam[1] < 0 || bary_lam[2] < 0 || bary_lam[3] < 0) {
          bary_ok = false;
          break;
        }
      }
      if (!bary_ok) continue;

      // If bary_ok, find c_core that satisfies transfer hineq:
      // hineq: w_sq * (u_sq - c_cone^2) <= u_sq * (lam * c_cone - c_core)^2
      // margin: lam * c_cone - c_core >= 0  =>  c_core <= lam * c_cone
      BigRat min_margin_sq = w_sq * (u_sq - c_cone * c_cone) / u_sq;
      if (min_margin_sq < 0) min_margin_sq = BigRat(0);
      double min_margin = std::sqrt(min_margin_sq.ToDouble());
      double max_c_core = lam.ToDouble() * c_cone.ToDouble() - min_margin;
      if (max_c_core <= deltas[0].ToDouble()) continue;

      BigRat c_core = deltas[0] + BigRat(1, 10000);
      if (c_core.ToDouble() > max_c_core) continue;

      // Now check annular dominance and angle bounds:
      // r_min must satisfy core_angle: r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
      // so r_min <= 2 * (c_core - delta) / sqrt(1 + (c_core - delta)^2) ~ 2 * (c_core - delta)
      BigRat c_core_eff = c_core - deltas[0];
      BigRat max_rmin_sq = BigRat(4) * c_core_eff * c_core_eff / (BigRat(1) + c_core_eff * c_core_eff);

      // And r must satisfy comp_angle: r^2 * (1 + (c_comp - delta)^2) <= 4 * (c_comp - delta)^2
      BigRat c_comp_eff = c_comp_test - deltas[0];
      BigRat max_r_sq = BigRat(4) * c_comp_eff * c_comp_eff / (BigRat(1) + c_comp_eff * c_comp_eff);

      std::cout << "  Candidate c_cone = " << c_cone.ToDouble()
                << " bary=OK max_c_core = " << max_c_core
                << " c_core_eff = " << c_core_eff.ToDouble() << "\n";
      found = true;
      break;
    }
    if (!found) {
      std::cout << "  No parameter set found for node " << path << " with this core axis!\n";
    }
  }

  return 0;
}
