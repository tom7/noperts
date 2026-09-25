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
  std::string path = "03121303021";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo contacts[4][3] = {
    // Axis 0: sib0
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14)},
    // Axis 1: sib1
    {MakeContact(15, 19, 19, 3, 200, 19), MakeContact(2, 1, 1, 4, 200, 1), MakeContact(8, 9, 9, 10, 200, 9)},
    // Axis 2: sib2
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15)},
    // Axis 3: cert_hull
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(10, 15, 15, 19, 800, 15)}
  };

  BigVecQ3 centers[4];
  BigRat deltas[4];
  AxisCertificate axes[4];
  for (int a = 0; a < 4; a++) {
    std::string err;
    BigRat max_def = (a == 0) ? BigRat(1, 1000) : BigRat(0);
    bool ok = Tube229::AuditAxis(tri, contacts[a], &axes[a], &centers[a], &deltas[a], &err, max_def);
    std::cout << "Axis " << a << " audit ok=" << ok << " fail=" << err << "\n";
    if (!ok) return 1;
    std::cout << "  Center " << a << ": (" << centers[a].x.ToDouble() << ", "
              << centers[a].y.ToDouble() << ", " << centers[a].z.ToDouble() << ")\n";
  }

  BigRat lam[4];
  BigVecQ3 origin(BigRat(0), BigRat(0), BigRat(0));
  bool caged = Bary4(centers, origin, lam);
  std::cout << "Caged origin: " << (caged ? "YES" : "NO") << "\n";
  if (caged) {
    std::cout << "  lambda = [" << lam[0].ToDouble() << ", " << lam[1].ToDouble()
              << ", " << lam[2].ToDouble() << ", " << lam[3].ToDouble() << "]\n";
  }
  for (int a = 0; a < 4; a++) {
    std::cout << "  delta " << a << " = " << deltas[a].ToDouble() << "\n";
  }
  BigRat r_cage = Tube229::ExactTetrahedronAxisRadius(centers);
  std::cout << "r_cage = " << r_cage.ToDouble() << "\n";

  // Test FindHullSupportAxis:
  AxisCertificate inner_core;
  BigVecQ3 inner_center;
  BigRat inner_delta;
  std::string hull_fail;
  bool hull_ok = Tube229::FindHullSupportAxis(tri, &inner_core, &inner_center, &inner_delta, &hull_fail);
  std::cout << "FindHullSupportAxis ok=" << hull_ok << " fail=" << hull_fail << "\n";
  if (hull_ok) {
    std::cout << "Inner core center: (" << inner_center.x.ToDouble() << ", "
              << inner_center.y.ToDouble() << ", " << inner_center.z.ToDouble() << ")\n";
    std::cout << "Inner core contacts: ("
              << inner_core.contacts[0].vertex << ", "
              << inner_core.contacts[1].vertex << ", "
              << inner_core.contacts[2].vertex << ")\n";
  }

  // Evaluate defect and annular dominance on Axis 0:
  AxisCertificate ax0_cert;
  BigVecQ3 c0_center;
  BigRat d0_delta;
  std::string ax0_err;
  // We can audit Axis 0 with relaxed defect:
  // Let's compute B and D of Axis 0:
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
  BigRat sum_w_upper0(0);
  for (int m = 0; m < 3; m++) {
    BigRat w_max = BigVecQ3::Dot(tri.corners[0], w_coeffs0[m]);
    for (int c = 1; c < 3; c++) {
      BigRat val = BigVecQ3::Dot(tri.corners[c], w_coeffs0[m]);
      if (val > w_max) w_max = val;
    }
    w_upper0[m] = w_max;
    sum_w_upper0 = sum_w_upper0 + w_max;
  }
  BigRat B0 = sum_w_upper0 * BigRat(2);
  BigRat total_defect0(0);
  for (int m = 0; m < 3; m++) {
    int sel = contacts[0][m].vertex;
    BigVecQ3 v_sel = Tube229::VertexQ(sel);
    BigRat max_m_defect(0);
    for (int k = 0; k < 20; k++) {
      bool tie = (k == sel) ||
                 (contacts[0][m].mix == 1000 && sel == contacts[0][m].edge_finish && k == contacts[0][m].edge_start) ||
                 (contacts[0][m].mix == 0 && sel == contacts[0][m].edge_start2 && k == contacts[0][m].edge_finish2);
      if (tie) continue;
      BigVecQ3 delta_v = Tube229::VertexQ(k) - v_sel;
      BigVecQ3 s_coeff = BigVecQ3::Cross(edges0[m], delta_v);
      BigRat max_s = BigVecQ3::Dot(tri.corners[0], s_coeff);
      for (int c = 1; c < 3; c++) {
        BigRat val = BigVecQ3::Dot(tri.corners[c], s_coeff);
        if (val > max_s) max_s = val;
      }
      if (max_s > max_m_defect) max_m_defect = max_s;
    }
    total_defect0 = total_defect0 + max_m_defect * w_upper0[m];
  }
  std::cout << "Axis 0 B = " << B0.ToDouble() << ", defect D = " << total_defect0.ToDouble() << "\n";

  // Check annular dominance with r_min and r:
  for (int r_denom : {500, 1000, 2000}) {
    for (int r_min_denom : {2000, 5000, 10000, 20000}) {
      if (r_min_denom <= r_denom) continue;
      BigRat r_min(1, r_min_denom);
      BigRat r(1, r_denom);
      // For c_cone:
        for (double c_thresh : {0.5, 0.7, 0.9, 0.95, 0.99, 0.999}) {
        BigRat c_cone = BigRat::FromDouble(c_thresh);
        BigRat delta(1, 1000);
        bool dom = Tube229::CheckAnnularDominance(B0, total_defect0, c_cone, delta, &r_min, &r);
        if (dom) {
          std::cout << "ANNULAR DOMINANCE! r_min=1/" << r_min_denom << " r=1/" << r_denom
                    << " c_cone=" << c_thresh << "\n";
        }
      }
    }
  }

  return 0;
}
