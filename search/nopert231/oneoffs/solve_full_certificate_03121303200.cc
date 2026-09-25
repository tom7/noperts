#include <iostream>
#include <iomanip>
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

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  int m[12] = {
    150, 1000, 882,
    50, 800, 950,
    1000, 1000, 343,
    113, 320, 150
  };

  ContactInfo c[4][3] = {
    { MakeContact(3, 2, 2, 1, m[0], 2),
      MakeContact(1, 4, 4, 8, m[1], 4),
      MakeContact(13, 14, 14, 15, m[2], 14) },
    { MakeContact(2, 1, 1, 4, m[3], 1),
      MakeContact(10, 15, 15, 19, m[4], 15),
      MakeContact(19, 3, 3, 2, m[5], 3) },
    { MakeContact(2, 1, 1, 4, m[6], 1),
      MakeContact(8, 9, 9, 10, m[7], 9),
      MakeContact(9, 10, 10, 15, m[8], 10) },
    { MakeContact(3, 2, 2, 1, m[9], 2),
      MakeContact(1, 4, 4, 8, m[10], 4),
      MakeContact(10, 15, 15, 19, m[11], 15) }
  };

  std::string err;
  AxisCertificate ax[4];
  BigVecQ3 cnt[4];
  BigRat var_radius[4];

  // Axis 0 has defect ~ 1.2e-4, axes 1, 2, 3 have zero defect
  if (!Tube229::AuditAxis(tri, c[0], &ax[0], &cnt[0], &var_radius[0], &err, BigRat(5, 10000))) {
    std::cerr << "Audit failed for axis 0: " << err << "\n";
    return 1;
  }
  for (int a = 1; a < 4; a++) {
    if (!Tube229::AuditAxis(tri, c[a], &ax[a], &cnt[a], &var_radius[a], &err, BigRat(0))) {
      std::cerr << "Audit failed for zero-defect axis " << a << ": " << err << "\n";
      return 1;
    }
  }

  // Core axis:
  ContactInfo core_contacts[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate core_ax;
  BigVecQ3 core_cnt;
  BigRat core_var;
  if (!Tube229::AuditAxis(tri, core_contacts, &core_ax, &core_cnt, &core_var, &err, BigRat(0))) {
    std::cerr << "Audit failed for core axis: " << err << "\n";
    return 1;
  }

  std::cout << "All 4 axes and core axis audited successfully!\n";

  // cnt[0] and core_cnt are ALREADY divided by B in AuditAxis (approxNormalizedCenter)
  BigVecQ3 u0 = cnt[0];
  BigVecQ3 u_core = core_cnt;

  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  BigRat dot0_core = u0.x * u_core.x + u0.y * u_core.y + u0.z * u_core.z;
  BigRat u_core_sq = u_core.x * u_core.x + u_core.y * u_core.y + u_core.z * u_core.z;

  double dot_val = dot0_core.ToDouble() / std::sqrt(u0_sq.ToDouble() * u_core_sq.ToDouble());
  std::cout << "cos(angle(u0, core)) = " << dot_val << " (" << std::acos(dot_val) * 180.0 / M_PI << " deg)\n";

  BigRat support_error(1, 100000000); // 100 * kappa
  BigRat defect0[3] = {BigRat(0), BigRat(0), BigRat(0)};

  // For ax[0], compute max s_upper for each chord i:
  BigVecQ3 edges0[3];
  for (int i = 0; i < 3; i++) {
    edges0[i] = Tube229::GetExactEdge(c[0][i]);
  }

  for (int i = 0; i < 3; i++) {
    int sel = c[0][i].vertex;
    BigVecQ3 v_sel = Tube229::VertexQ(sel);
    BigRat max_supp(0);
    for (int k = 0; k < 20; k++) {
      bool tie = (k == sel) ||
                 (c[0][i].mix == 1000 && sel == c[0][i].edge_finish && k == c[0][i].edge_start) ||
                 (c[0][i].mix == 0 && sel == c[0][i].edge_start2 && k == c[0][i].edge_finish2);
      if (tie) continue;
      BigVecQ3 v_k = Tube229::VertexQ(k);
      BigVecQ3 diff = v_k - v_sel;
      BigVecQ3 s_coeff = BigVecQ3::Cross(edges0[i], diff);
      BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
      for (int cn = 1; cn < 3; cn++) {
        BigRat val = BigVecQ3::Dot(tri.corners[cn], s_coeff);
        if (val > max_s) max_s = val;
      }
      BigRat s_upper = max_s + support_error;
      if (s_upper > max_supp) max_supp = s_upper;
    }
    defect0[i] = max_supp;
    std::cout << "defect0[" << i << "] = " << defect0[i].ToString()
              << " (" << defect0[i].ToDouble() << ")\n";
  }

  // Weight budget and D0:
  // In Lean: defect_budget0 : (∑ i, box.weightUpper 0 i * defect0 i) ≤ D0
  // In tube229, weightUpper is computed from weights.
  // We can compute weightUpper(ax0, i):
  BigRat D0 = defect0[2];
  BigRat lam = dot0_core / u0_sq;
  BigVecQ3 w = {u_core.x - lam * u0.x, u_core.y - lam * u0.y, u_core.z - lam * u0.z};
  BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

  std::cout << "lam = " << lam.ToDouble() << "\n";
  std::cout << "w_sq = " << w_sq.ToDouble() << ", u0_sq = " << u0_sq.ToDouble() << "\n";

  BigRat delta(234013, 1000000000);
  BigRat box_r(4, 100000); // 0.00004
  BigRat box_c(1, 1000);   // 0.001

  // First check what range of c_cone makes the cage barycentric valid:
  std::cout << "--- Sweeping c_cone for octahedron enclosure ---\n";
  BigRat R = BigRat(7, 4) * (box_c + delta);
  BigVecQ3 oct[6] = {
    {R, BigRat(0), BigRat(0)},
    {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)},
    {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R},
    {BigRat(0), BigRat(0), -R}
  };

  BigRat max_valid_c_cone(0);
  for (int ci = 10; ci <= 300; ci += 5) {
    BigRat test_c_cone(ci, 10000); // 0.001 to 0.030
    BigRat scale_0 = (box_c + delta) / test_c_cone;
    BigVecQ3 v[4];
    v[0] = {u0.x * scale_0, u0.y * scale_0, u0.z * scale_0};
    for (int a = 1; a < 4; a++) {
      v[a] = cnt[a];
    }
    BigVecQ3 d0 = v[0] - v[3];
    BigVecQ3 d1 = v[1] - v[3];
    BigVecQ3 d2 = v[2] - v[3];
    BigRat det = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, d2));
    if (det == 0) continue;

    bool all_pos = true;
    BigRat min_l(100);
    for (int o = 0; o < 6; o++) {
      BigVecQ3 dp = oct[o] - v[3];
      BigRat l0 = BigVecQ3::Dot(dp, BigVecQ3::Cross(d1, d2)) / det;
      BigRat l1 = BigVecQ3::Dot(d0, BigVecQ3::Cross(dp, d2)) / det;
      BigRat l2 = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, dp)) / det;
      BigRat l3 = BigRat(1) - l0 - l1 - l2;
      BigRat ml = std::min({l0, l1, l2, l3});
      if (ml < min_l) min_l = ml;
      if (l0 <= 0 || l1 <= 0 || l2 <= 0 || l3 <= 0) all_pos = false;
    }
    if (all_pos) {
      max_valid_c_cone = test_c_cone;
      std::cout << "c_cone = " << test_c_cone.ToDouble() << ": VALID! min_l = " << min_l.ToDouble() << "\n";
    }
  }
  std::cout << "Max valid c_cone for cage = " << max_valid_c_cone.ToDouble() << "\n";

  // Sweep c_cone and c_core:
  std::cout << "Testing parameter combinations (c_cone, c_core):\n";
  for (int c_cone_i = 10; c_cone_i <= 100; c_cone_i += 5) {
    BigRat c_cone(c_cone_i, 1000);
    for (int c_core_i = 1; c_core_i <= 50; c_core_i += 2) {
      BigRat c_core(c_core_i, 10000);
      BigRat margin = lam * c_cone - c_core;
      if (margin < 0) continue;

      BigRat lhs_proj = w_sq * (u0_sq - c_cone * c_cone);
      BigRat rhs_proj = u0_sq * margin * margin;
      if (lhs_proj > rhs_proj) continue;

      // Projective condition passed! Now test r_min for annular dominance and core_angle:
      // r_min must satisfy core_angle:
      // r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
      // so r_min <= 2 * (c_core - delta) / sqrt(1 + (c_core - delta)^2) ~ 2 * (c_core - delta).
      // Also annular dominance:
      // ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4)*r^2) * ((c_cone - delta)^2 * B0^2)
      // So r_min >= ((1/2)*r^2*B0 + D0) / ((c_cone - delta) * B0 * sqrt(1 - (1/4)*r^2)).
      if (c_core <= delta) continue;
      BigRat diff_core = c_core - delta;
      BigRat diff_cone = c_cone - delta;

      BigRat B0 = ax[0].B;
      BigRat num = BigRat(1, 2) * box_r * box_r * B0 + D0;
      BigRat r_min_needed = num / (diff_cone * B0);

      // Check if r_min_needed satisfies core_angle:
      BigRat lhs_core = r_min_needed * r_min_needed * (BigRat(1) + diff_core * diff_core);
      BigRat rhs_core = BigRat(4) * diff_core * diff_core;

      if (lhs_core <= rhs_core) {
        std::cout << "FOUND MATCHING PARAMETERS!\n"
                  << "  c_cone = " << c_cone.ToDouble() << " (" << c_cone.ToString() << ")\n"
                  << "  c_core = " << c_core.ToDouble() << " (" << c_core.ToString() << ")\n"
                  << "  r_min_needed = " << r_min_needed.ToDouble() << "\n"
                  << "  margin = " << margin.ToDouble() << "\n"
                  << "  proj: lhs=" << lhs_proj.ToDouble() << " <= rhs=" << rhs_proj.ToDouble() << "\n";

        // Check barycentric coordinates for all 6 octahedron vertices:
        BigVecQ3 v[4];
        BigRat scale_0 = (box_c + delta) / c_cone;
        v[0] = {u0.x * scale_0, u0.y * scale_0, u0.z * scale_0};
        for (int a = 1; a < 4; a++) {
          v[a] = cnt[a];
        }

        // Test barycentric coordinates of octahedron:
        BigRat R = BigRat(7, 4) * (box_c + delta);
        BigVecQ3 oct[6] = {
          {R, BigRat(0), BigRat(0)},
          {-R, BigRat(0), BigRat(0)},
          {BigRat(0), R, BigRat(0)},
          {BigRat(0), -R, BigRat(0)},
          {BigRat(0), BigRat(0), R},
          {BigRat(0), BigRat(0), -R}
        };

        // Solve v_mat * l = p:
        // det = det(v0 - v3, v1 - v3, v2 - v3)
        BigVecQ3 d0 = v[0] - v[3];
        BigVecQ3 d1 = v[1] - v[3];
        BigVecQ3 d2 = v[2] - v[3];
        BigRat det = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, d2));
        std::cout << "bary det = " << det.ToDouble() << "\n";

        bool all_pos = true;
        BigRat min_l(100);
        for (int o = 0; o < 6; o++) {
          BigVecQ3 dp = oct[o] - v[3];
          BigRat l0 = BigVecQ3::Dot(dp, BigVecQ3::Cross(d1, d2)) / det;
          BigRat l1 = BigVecQ3::Dot(d0, BigVecQ3::Cross(dp, d2)) / det;
          BigRat l2 = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, dp)) / det;
          BigRat l3 = BigRat(1) - l0 - l1 - l2;
          BigRat ml = std::min({l0, l1, l2, l3});
          if (ml < min_l) min_l = ml;
          if (l0 <= 0 || l1 <= 0 || l2 <= 0 || l3 <= 0) all_pos = false;
        }
        std::cout << "All octahedron vertices inside? " << (all_pos ? "YES" : "NO")
                  << ", min_l = " << min_l.ToDouble() << " (" << min_l.ToString() << ")\n";
        return 0;
      }
    }
  }

  std::cout << "No matching (c_cone, c_core) in standard grid.\n";
  return 0;
}
