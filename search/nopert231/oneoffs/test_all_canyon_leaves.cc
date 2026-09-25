#include <iostream>
#include <string>
#include <vector>
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

  for (const auto &path : leaves) {
    std::cout << "\n========================================\n";
    std::cout << "Testing leaf " << path << " (depth " << path.size() - 1 << "):\n";
    TriangleQ tri = TriangleFromPath(path);

    BigVecQ3 centers[4];
    BigRat deltas[4];
    AxisCertificate axes[4];
    bool audit_ok = true;
    for (int a = 0; a < 4; a++) {
      std::string err;
      BigRat max_def = (a == 0) ? BigRat(5, 1000) : BigRat(0);
      bool ok = Tube229::AuditAxis(tri, contacts[a], &axes[a], &centers[a], &deltas[a], &err, max_def);
      if (!ok) {
        std::cout << "  Axis " << a << " audit FAILED: " << err << "\n";
        audit_ok = false;
        break;
      }
    }
    if (!audit_ok) continue;

    BigRat lam[4];
    BigVecQ3 origin(BigRat(0), BigRat(0), BigRat(0));
    bool caged = Bary4(centers, origin, lam);
    std::cout << "  Caged origin: " << (caged ? "YES" : "NO") << "\n";
    if (caged) {
      std::cout << "    lambda = [" << lam[0].ToDouble() << ", " << lam[1].ToDouble()
                << ", " << lam[2].ToDouble() << ", " << lam[3].ToDouble() << "]\n";
    }
    BigRat max_delta = deltas[0];
    for (int a = 1; a < 4; a++) if (deltas[a] > max_delta) max_delta = deltas[a];
    BigRat r_cage = Tube229::ExactTetrahedronAxisRadius(centers);
    BigRat c_eff = r_cage - max_delta;
    std::cout << "  r_cage = " << r_cage.ToDouble() << " max_delta = " << max_delta.ToDouble()
              << " c_eff = " << c_eff.ToDouble() << "\n";

    // Defect D0
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
    std::cout << "  D0 = " << D0.ToDouble() << " (" << D0.ToString() << ")"
              << " delta0 = " << deltas[0].ToDouble() << "\n";
    // Test rational decomposition: v = lambda * u + w
    // u = approxNormalizedCenter 0 = centers[0] / B0
    // v = approxNormalizedCenter 3 = centers[3] / B3
    BigVecQ3 u = centers[0];
    BigVecQ3 v = centers[3];
    BigRat u_sq = BigVecQ3::Dot(u, u);
    BigRat v_sq = BigVecQ3::Dot(v, v);
    BigRat uv = BigVecQ3::Dot(u, v);
    BigRat lambda = uv / u_sq;
    BigRat w_sq = v_sq - lambda * lambda * u_sq;
    BigVecQ3 w = v - u * lambda;
    double u_len = std::sqrt(u_sq.ToDouble());
    double v_len = std::sqrt(v_sq.ToDouble());
    // Test rational cone containment inequality:
    // u = approxNormalizedCenter 0, v = approxNormalizedCenter 3
    // lambda = (u.v) / (u.u)
    // w_sq = v.v - lambda^2 * u.u
    // Print exact rational decomposition for Lean certificate:
    std::cout << "  u_len=" << u_len << " v_len=" << v_len
              << " cos=" << (uv.ToDouble() / (u_len * v_len))
              << " lambda=" << lambda.ToDouble() << "\n";
    for (double c_val : {0.01, 0.02, 0.03, 0.04, 0.045, 0.05, 0.055, 0.06, 0.065, 0.07}) {
      BigRat c_cone_rat = BigRat::FromDouble(c_val);
      BigRat c_core_rat(1, 10000);
      BigRat margin = lambda * c_cone_rat - c_core_rat;
      BigRat lhs = margin * margin * u_sq;
      BigRat rhs = w_sq * (u_sq - c_cone_rat * c_cone_rat);
      std::cout << "  c=" << c_val << " margin=" << margin.ToDouble()
                << " lhs=" << lhs.ToDouble() << " rhs=" << rhs.ToDouble()
                << " ok=" << (lhs >= rhs && margin >= 0 && (u_sq >= c_cone_rat * c_cone_rat)) << "\n";
    }

    // Annular dominance
    // Test annular dominance with small cage inradius c:
    for (double c_cage : {0.003, 0.004, 0.0045}) {
      BigRat c_rat = BigRat::FromDouble(c_cage);
      for (int rm_denom : {30, 40, 50, 60, 80, 100, 150, 200}) {
        for (int r_denom : {30, 40, 50, 60, 80, 100, 150, 200}) {
          if (rm_denom < r_denom) continue;
          BigRat r_min(1, rm_denom);
          BigRat r(1, r_denom);
          if (Tube229::CheckAnnularDominance(axes[0].B, D0, c_rat, deltas[0], &r_min, &r)) {
            std::cout << "  CAGE DOMINANCE at c=" << c_cage << ": r_min=1/" << rm_denom
                      << " r=1/" << r_denom << "\n";
            goto found_cage_dom;
          }
        }
      }
      found_cage_dom:;
    }
  }

  return 0;
}
