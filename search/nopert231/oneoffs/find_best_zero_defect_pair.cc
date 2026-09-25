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

static BigRat CeilTo(const BigRat &r, int64_t denom) {
  BigRat scaled = r * BigRat(denom);
  int64_t c = (int64_t)std::ceil(scaled.ToDouble());
  return BigRat(c, denom);
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Zero-defect annular axis:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };

  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  if (!Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0))) {
    std::cout << "Annular audit failed: " << err << "\n";
    return 1;
  }

  BigVecQ3 u_ann = {ctr_ann.x / ax_ann.B, ctr_ann.y / ax_ann.B, ctr_ann.z / ax_ann.B};
  BigRat u0_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  double u0_norm = std::sqrt(u0_sq.ToDouble());

  // Complement axes:
  ContactInfo comp0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(14, 15, 15, 19, 600, 15)
  };
  ContactInfo comp1[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 600, 8),
    MakeContact(14, 15, 15, 19, 200, 15)
  };
  ContactInfo comp2[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(10, 15, 15, 19, 600, 15),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_comp[3];
  BigVecQ3 ctr_comp[3];
  BigRat del_comp[3];
  Tube229::AuditAxis(tri, comp0, &ax_comp[0], &ctr_comp[0], &del_comp[0], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp1, &ax_comp[1], &ctr_comp[1], &del_comp[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, comp2, &ax_comp[2], &ctr_comp[2], &del_comp[2], &err, BigRat(0));

  BigRat max_del = del_ann;
  for (int a = 0; a < 3; a++) {
    if (del_comp[a] > max_del) max_del = del_comp[a];
  }

  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Auditing " << axes.size() << " hull axes against all Lean conditions...\n";

  int best_idx = -1;
  double best_margin_ratio = 0;
  double best_c_cone_val = 0;
  BigRat best_del_val;

  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i].cert;
    const auto &ctr = axes[i].center;
    const auto &del = axes[i].delta;

    BigRat delta_req = max_del;
    if (del > delta_req) delta_req = del;
    BigRat delta = CeilTo(delta_req, 10000LL);

    BigVecQ3 u_core = {ctr.x / ax.B, ctr.y / ax.B, ctr.z / ax.B};
    BigRat dot = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
    BigRat lam = dot / u0_sq;
    if (lam <= 0) continue;

    BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};
    BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

    for (double c_c = delta.ToDouble() + 0.0005; c_c < u0_norm; c_c += 0.0005) {
      BigRat c_cone = BigRat::FromDouble(c_c);
      BigRat c_core = delta + BigRat(1, 2000);
      BigRat c_comp = delta + BigRat(1, 2000);

      BigRat r = BigRat(1, 2000);
      BigRat r_min = BigRat(1, 10000);

      // Check core_angle
      BigRat c_core_diff = c_core - delta;
      BigRat ca_lhs = r_min * r_min * (BigRat(1) + c_core_diff * c_core_diff);
      BigRat ca_rhs = BigRat(4) * c_core_diff * c_core_diff;
      if (ca_lhs > ca_rhs) continue;

      // Check comp_angle
      BigRat c_comp_diff = c_comp - delta;
      BigRat comp_lhs = r * r * (BigRat(1) + c_comp_diff * c_comp_diff);
      BigRat comp_rhs = BigRat(4) * c_comp_diff * c_comp_diff;
      if (comp_lhs > comp_rhs) continue;

      // Check annular dominance (with D0 = 0!)
      BigRat D0 = BigRat(0);
      BigRat term1 = BigRat(1, 2) * r * r * ax_ann.B + D0;
      BigRat ad_lhs = term1 * term1;
      BigRat term2 = (c_cone - delta) * ax_ann.B;
      BigRat ad_rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (term2 * term2);
      if (ad_lhs > ad_rhs) continue;

      // Check hineq
      BigRat margin = lam * c_cone - c_core;
      if (margin <= 0) continue;
      BigRat proj_lhs = w_sq * (u0_sq - c_cone * c_cone);
      BigRat proj_rhs = u0_sq * margin * margin;
      if (proj_lhs <= proj_rhs) {
        double ratio = proj_rhs.ToDouble() / std::max(1e-15, proj_lhs.ToDouble());
        if (ratio > best_margin_ratio) {
          best_margin_ratio = ratio;
          best_idx = (int)i;
          best_c_cone_val = c_c;
          best_del_val = delta;
        }
      }
    }
  }

  std::cout << "Best axis index: " << best_idx << "\n";
  std::cout << "Best margin ratio (rhs/lhs): " << best_margin_ratio << "\n";
  std::cout << "Best c_cone: " << best_c_cone_val << "\n";
  std::cout << "Best delta: " << best_del_val.ToString() << " (" << best_del_val.ToDouble() << ")\n";

  if (best_idx >= 0) {
    const auto &ax = axes[best_idx];
    std::cout << "Contacts:\n";
    for (int m = 0; m < 3; m++) {
      std::cout << "  {" << ax.cert.contacts[m].edge_start << ", "
                << ax.cert.contacts[m].edge_finish << ", "
                << ax.cert.contacts[m].edge_start2 << ", "
                << ax.cert.contacts[m].edge_finish2 << ", "
                << ax.cert.contacts[m].mix << ", "
                << ax.cert.contacts[m].vertex << "}\n";
    }
    std::cout << "B = " << ax.cert.B.ToString() << "\n";
    std::cout << "center = (" << ax.center.x.ToString() << ", "
              << ax.center.y.ToString() << ", "
              << ax.center.z.ToString() << ")\n";
    std::cout << "delta = " << ax.delta.ToString() << "\n";
  }

  return 0;
}
