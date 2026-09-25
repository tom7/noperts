#include <iostream>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  ContactInfo contacts_core[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };

  AxisCertificate ax0, ax_core;
  BigVecQ3 ctr0, ctr_core;
  BigRat del0, del_core;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, contacts_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

  BigVecQ3 u0 = ctr0;
  BigVecQ3 v0 = ctr_core;

  std::cout << "u0.x = " << u0.x.ToString() << "\n";
  std::cout << "u0.y = " << u0.y.ToString() << "\n";
  std::cout << "u0.z = " << u0.z.ToString() << "\n";

  std::cout << "v0.x = " << v0.x.ToString() << "\n";
  std::cout << "v0.y = " << v0.y.ToString() << "\n";
  std::cout << "v0.z = " << v0.z.ToString() << "\n";

  BigRat u0_sq = BigVecQ3::Dot(u0, u0);
  BigRat v0_dot_u0 = BigVecQ3::Dot(v0, u0);
  BigRat lam = v0_dot_u0 / u0_sq;

  BigVecQ3 w = v0 - (u0 * lam);

  std::cout << "lam = " << lam.ToString() << "\n";
  std::cout << "w.x = " << w.x.ToString() << "\n";
  std::cout << "w.y = " << w.y.ToString() << "\n";
  std::cout << "w.z = " << w.z.ToString() << "\n";

  BigRat w_dot_u0 = BigVecQ3::Dot(w, u0);
  std::cout << "w . u0 = " << w_dot_u0.ToString() << " (must be 0)\n";

  BigRat w_sq = BigVecQ3::Dot(w, w);
  std::cout << "u0_sq = " << u0_sq.ToString() << " (double: " << u0_sq.ToDouble() << ")\n";
  std::cout << "w_sq = " << w_sq.ToString() << " (double: " << w_sq.ToDouble() << ")\n";

  // Now test with c_cone = 396/10000 = 99/2500, c_core = 3/10000
  BigRat c_cone_val(99, 2500); // 0.0396
  BigRat c_core_val(3, 10000); // 0.0003

  BigRat diff_term = lam * c_cone_val - c_core_val;
  std::cout << "lam * c_cone - c_core = " << diff_term.ToString() << " (double: " << diff_term.ToDouble() << ")\n";

  BigRat hineq_lhs = w_sq * (u0_sq - c_cone_val * c_cone_val);
  BigRat hineq_rhs = u0_sq * (diff_term * diff_term);
  std::cout << "hineq_lhs = " << hineq_lhs.ToDouble() << "\n";
  std::cout << "hineq_rhs = " << hineq_rhs.ToDouble() << "\n";
  std::cout << "hineq holds (lhs <= rhs): " << (hineq_lhs <= hineq_rhs) << " (diff rhs - lhs = " << (hineq_rhs - hineq_lhs).ToDouble() << ")\n";

  return 0;
}
