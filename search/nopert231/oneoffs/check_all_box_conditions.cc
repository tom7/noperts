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
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  AxisCertificate ax1; BigVecQ3 ctr1; BigRat del1;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(5, 1000));

  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax2; BigVecQ3 ctr2; BigRat del2;
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(5, 1000));

  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax3; BigVecQ3 ctr3; BigRat del3;
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(5, 1000));

  ContactInfo contacts_core[3] = {
    MakeContact(15, 19, 19, 3, 900, 19),
    MakeContact(3, 2, 2, 1, 333, 2),
    MakeContact(4, 8, 8, 9, 1000, 8)
  };
  AxisCertificate ax_core; BigVecQ3 ctr_core; BigRat del_core;
  Tube229::AuditAxis(tri, contacts_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

  BigRat delta = BigRat(21, 10000); // 0.0021
  BigRat c_core = BigRat(4, 1000);  // 0.004
  BigRat c_cone = BigRat(42, 1000); // 0.042
  BigRat r = BigRat(1, 2000);
  BigRat r_min = BigRat(1, 10000);
  BigRat c_comp = BigRat(5, 1000);  // 0.005

  // 1. Check deltas
  std::cout << "del0 <= delta: " << (del0 <= delta) << "\n";
  std::cout << "del1 <= delta: " << (del1 <= delta) << "\n";
  std::cout << "del2 <= delta: " << (del2 <= delta) << "\n";
  std::cout << "del3 <= delta: " << (del3 <= delta) << "\n";
  std::cout << "del_core <= delta: " << (del_core <= delta) << "\n";

  // 2. Check c_core_margin: delta <= c_core
  std::cout << "delta <= c_core: " << (delta <= c_core) << "\n";

  // 3. Check c_cone_margin: delta <= c_cone
  std::cout << "delta <= c_cone: " << (delta <= c_cone) << "\n";

  // 4. Check c_margin: delta <= c_comp
  std::cout << "delta <= c_comp: " << (delta <= c_comp) << "\n";

  // 5. core_angle: r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
  BigRat c_core_diff = c_core - delta;
  BigRat ca_lhs = r_min * r_min * (BigRat(1) + c_core_diff * c_core_diff);
  BigRat ca_rhs = BigRat(4) * c_core_diff * c_core_diff;
  std::cout << "core_angle: " << (ca_lhs <= ca_rhs)
            << " (lhs=" << ca_lhs.ToDouble() << ", rhs=" << ca_rhs.ToDouble() << ")\n";

  // 6. comp_angle: r^2 * (1 + (c_comp - delta)^2) <= 4 * (c_comp - delta)^2
  BigRat c_comp_diff = c_comp - delta;
  BigRat comp_lhs = r * r * (BigRat(1) + c_comp_diff * c_comp_diff);
  BigRat comp_rhs = BigRat(4) * c_comp_diff * c_comp_diff;
  std::cout << "comp_angle: " << (comp_lhs <= comp_rhs)
            << " (lhs=" << comp_lhs.ToDouble() << ", rhs=" << comp_rhs.ToDouble() << ")\n";

  // 7. Annular dominance:
  // ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4)*r^2) * ((c_cone - delta)^2 * B0^2)
  BigRat D0 = BigRat(2, 10000000); // 2e-7
  BigRat term1 = BigRat(1, 2) * r * r * ax0.B + D0;
  BigRat ad_lhs = term1 * term1;
  BigRat term2 = (c_cone - delta) * ax0.B;
  BigRat ad_rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (term2 * term2);
  std::cout << "annular_dominance: " << (ad_lhs <= ad_rhs)
            << " (lhs=" << ad_lhs.ToDouble() << ", rhs=" << ad_rhs.ToDouble()
            << ", ratio=" << (ad_lhs.ToDouble() / ad_rhs.ToDouble()) << ")\n";

  // 8. Projection inequality hineq:
  BigVecQ3 u_ann = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigVecQ3 u_core = {ctr_core.x / ax_core.B, ctr_core.y / ax_core.B, ctr_core.z / ax_core.B};
  BigRat u0_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  BigRat dot = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
  BigRat lam = dot / u0_sq;
  BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};
  BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

  BigRat margin = lam * c_cone - c_core;
  BigRat proj_lhs = w_sq * (u0_sq - c_cone * c_cone);
  BigRat proj_rhs = u0_sq * margin * margin;
  std::cout << "hineq: " << (proj_lhs <= proj_rhs)
            << " (lhs=" << proj_lhs.ToDouble() << ", rhs=" << proj_rhs.ToDouble() << ")\n";

  return 0;
}
