#include <iostream>
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
  std::string path = "03121303022";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo contacts[4][3] = {
    // Axis 0 (annular, with v14)
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14)},
    // Axis 1
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 800, 15), MakeContact(3, 2, 2, 1, 1000, 2)},
    // Axis 2
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(8, 9, 9, 10, 1000, 9), MakeContact(15, 19, 19, 3, 0, 19)},
    // Axis 3
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(9, 10, 10, 15, 200, 10), MakeContact(10, 15, 15, 19, 0, 15)}
  };

  AxisCertificate axes[4];
  BigVecQ3 centers[4];
  BigRat deltas[4];
  for (int a = 0; a < 4; a++) {
    std::string err;
    BigRat max_def = (a == 0 ? BigRat(5, 1000) : BigRat(0));
    if (!Tube229::AuditAxis(tri, contacts[a], &axes[a], &centers[a], &deltas[a], &err, max_def)) {
      std::cout << "Audit failed for axis " << a << ": " << err << "\n";
      return 1;
    }
  }

  // Core axis:
  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate core_axis;
  BigVecQ3 core_center;
  BigRat core_delta;
  std::string err;
  if (!Tube229::AuditAxis(tri, core_contacts, &core_axis, &core_center, &core_delta, &err, BigRat(0))) {
    std::cout << "Core axis audit failed: " << err << "\n";
    return 1;
  }

  BigRat delta = deltas[0];
  for (int a = 1; a < 4; a++) if (deltas[a] > delta) delta = deltas[a];
  if (core_delta > delta) delta = core_delta;

  // Exact D0:
  BigRat D0(0);
  BigVecQ3 edges0[3] = {Tube229::GetExactEdge(contacts[0][0]), Tube229::GetExactEdge(contacts[0][1]), Tube229::GetExactEdge(contacts[0][2])};
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
      if (max_s > 0) {
        std::cout << "Contact m=" << m << " (sel=" << sel << "): vertex k=" << k
                  << " has positive defect = " << max_s.ToDouble() << "\n";
      }
      if (max_s > max_m_defect) max_m_defect = max_s;
    }
    D0 = D0 + max_m_defect * w_upper0[m];
  }

  BigRat inrad = Tube229::ExactTetrahedronAxisRadius(centers);
  std::cout << "Exact inradius = " << inrad.ToDouble() << "\n";
  std::cout << "Delta = " << delta.ToDouble() << "\n";
  std::cout << "D0 = " << D0.ToDouble() << "\n";

  // Test parameters:
  BigRat c(38, 1000); // 0.038
  BigRat r_min(1, 500); // 0.002
  BigRat r(1, 400); // 0.0025
  BigRat c_core(1, 1000); // 0.001

  // 1. Barycentric test:
  bool bary_ok = true;
  for (int k = 0; k < 6; k++) {
    BigVecQ3 target = BigVecQ3{BigRat(0), BigRat(0), BigRat(0)};
    BigRat scale = BigRat(7, 4) * (c + delta);
    if (k == 0) target.x = scale;
    else if (k == 1) target.x = -scale;
    else if (k == 2) target.y = scale;
    else if (k == 3) target.y = -scale;
    else if (k == 4) target.z = scale;
    else if (k == 5) target.z = -scale;

    BigVecQ3 v0 = centers[0] - centers[3];
    BigVecQ3 v1 = centers[1] - centers[3];
    BigVecQ3 v2 = centers[2] - centers[3];
    BigVecQ3 w_tgt = target - centers[3];
    BigRat den = BigVecQ3::Det(v0, v1, v2);
    BigRat l0 = BigVecQ3::Det(w_tgt, v1, v2) / den;
    BigRat l1 = BigVecQ3::Det(v0, w_tgt, v2) / den;
    BigRat l2 = BigVecQ3::Det(v0, v1, w_tgt) / den;
    BigRat l3 = BigRat(1) - l0 - l1 - l2;
    if (l0 < 0 || l1 < 0 || l2 < 0 || l3 < 0) {
      bary_ok = false;
      std::cout << "Barycentric failed for vertex " << k << ": ("
                << l0.ToDouble() << ", " << l1.ToDouble() << ", " << l2.ToDouble() << ", " << l3.ToDouble() << ")\n";
    }
  }
  std::cout << "1. Barycentric Valid: " << (bary_ok ? "PASS" : "FAIL") << "\n";

  // 2. Annular dominance test:
  // ((1/2) r^2 B0 + D0)^2 <= r_min^2 (1 - (1/4) r^2) ((c - delta)^2 B0^2)
  BigRat lhs_term = BigRat(1, 2) * r * r * axes[0].B + D0;
  BigRat lhs = lhs_term * lhs_term;
  BigRat rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * ((c - delta) * (c - delta) * axes[0].B * axes[0].B);
  bool dom_ok = (lhs <= rhs);
  std::cout << "2. Annular Dominance: " << (dom_ok ? "PASS" : "FAIL")
            << " (lhs=" << lhs.ToDouble() << ", rhs=" << rhs.ToDouble() << ")\n";

  // 3. Orthogonal projection:
  BigVecQ3 u = centers[0];
  BigVecQ3 v = core_center;
  std::cout << "u = (" << u.x.ToDouble() << ", " << u.y.ToDouble() << ", " << u.z.ToDouble() << ") len=" << std::sqrt(BigVecQ3::Dot(u, u).ToDouble()) << "\n";
  std::cout << "v = (" << v.x.ToDouble() << ", " << v.y.ToDouble() << ", " << v.z.ToDouble() << ") len=" << std::sqrt(BigVecQ3::Dot(v, v).ToDouble()) << "\n";
  BigRat u_sq = BigVecQ3::Dot(u, u);
  BigRat uv = BigVecQ3::Dot(u, v);
  BigRat lambda = uv / u_sq;
  BigVecQ3 w_proj = v - u * lambda;
  BigRat w_sq = BigVecQ3::Dot(w_proj, w_proj);
  BigRat margin = lambda * c - c_core;
  BigRat proj_lhs = w_sq * (u_sq - c * c);
  BigRat proj_rhs = u_sq * margin * margin;
  bool proj_ok = (margin >= 0 && proj_lhs <= proj_rhs);
  std::cout << "3. Orthogonal Projection: " << (proj_ok ? "PASS" : "FAIL")
            << " (margin=" << margin.ToDouble() << ", lhs=" << proj_lhs.ToDouble() << ", rhs=" << proj_rhs.ToDouble() << ")\n";

  // 4. Angle bounds:
  // comp_angle: r^2 (1 + (c - delta)^2) <= 4 (c - delta)^2
  BigRat c_eff = c - delta;
  BigRat comp_lhs = r * r * (BigRat(1) + c_eff * c_eff);
  BigRat comp_rhs = BigRat(4) * c_eff * c_eff;
  bool comp_angle_ok = (comp_lhs <= comp_rhs);
  std::cout << "4. Complement Angle: " << (comp_angle_ok ? "PASS" : "FAIL") << "\n";

  // core_angle: r_min^2 (1 + (c_core - delta)^2) <= 4 (c_core - delta)^2
  BigRat c_core_eff = c_core - delta;
  BigRat core_lhs = r_min * r_min * (BigRat(1) + c_core_eff * c_core_eff);
  BigRat core_rhs = BigRat(4) * c_core_eff * c_core_eff;
  bool core_angle_ok = (core_lhs <= core_rhs);
  std::cout << "5. Core Angle: " << (core_angle_ok ? "PASS" : "FAIL") << "\n";

  return 0;
}
