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

  BigRat u0_sq = BigVecQ3::Dot(u0, u0);
  BigRat v0_dot_u0 = BigVecQ3::Dot(v0, u0);
  BigRat lam = v0_dot_u0 / u0_sq;
  BigVecQ3 w = v0 - (u0 * lam);
  BigRat w_sq = BigVecQ3::Dot(w, w);

  double norm_u0 = std::sqrt(u0_sq.ToDouble());
  double norm_v0 = std::sqrt(BigVecQ3::Dot(v0, v0).ToDouble());
  double norm_w = std::sqrt(w_sq.ToDouble());
  double sin_theta = norm_w / norm_v0;
  double theta = std::asin(sin_theta) * 180.0 / M_PI;

  std::cout << "||u0|| = " << norm_u0 << "\n";
  std::cout << "||v0|| = " << norm_v0 << "\n";
  std::cout << "theta = " << theta << " deg\n";
  std::cout << "Min c_cone needed for hineq: " << norm_u0 * sin_theta << "\n";

  BigRat c_core_val(3, 10000); // 0.0003

  for (double c_c = 0.0385; c_c <= 0.0405; c_c += 0.0002) {
    BigRat c_cone_val = BigRat::FromDouble(c_c);
    BigRat hineq_lhs = w_sq * (u0_sq - c_cone_val * c_cone_val);
    BigRat diff_term = lam * c_cone_val - c_core_val;
    BigRat hineq_rhs = u0_sq * (diff_term * diff_term);
    bool ok = (hineq_lhs <= hineq_rhs);
    std::cout << "c_cone = " << c_c << " hineq_ok = " << ok
              << " margin = " << (diff_term > 0)
              << " diff = " << (hineq_rhs - hineq_lhs).ToDouble() << "\n";
  }

  return 0;
}
