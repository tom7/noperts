#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"
#include "../cc-lib/bignum/big.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo contacts0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, contacts0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  int a = 2960;
  const auto &ax = valid_axes[a];
  std::cout << "Axis 2960 audit:\n";
  std::cout << "  B: " << ax.cert.B.ToString() << "\n";
  std::cout << "  delta: " << ax.delta.ToString() << "\n";
  std::cout << "  center.x: " << ax.center.x.ToString() << "\n";
  std::cout << "  center.y: " << ax.center.y.ToString() << "\n";
  std::cout << "  center.z: " << ax.center.z.ToString() << "\n";
  std::cout << "  witness: (" << ax.cert.nonzero_witness[0] << ", "
            << ax.cert.nonzero_witness[1] << ", " << ax.cert.nonzero_witness[2] << ")\n";
  for (int k = 0; k < 3; k++) {
    const auto &c = ax.cert.contacts[k];
    std::cout << "  contact " << k << ": ("
              << c.edge_start << "->" << c.edge_finish << " & "
              << c.edge_start2 << "->" << c.edge_finish2 << "), mix="
              << c.mix << ", v=" << c.vertex << "\n";
  }

  // u0 = ctr0 / B0
  // v = ax.center / ax.cert.B
  BigRat u0_x = BigRat::Div(ctr0.x, ax0.B);
  BigRat u0_y = BigRat::Div(ctr0.y, ax0.B);
  BigRat u0_z = BigRat::Div(ctr0.z, ax0.B);
  BigRat norm_u0_sq = BigRat::Plus(
    BigRat::Plus(BigRat::Times(u0_x, u0_x), BigRat::Times(u0_y, u0_y)),
    BigRat::Times(u0_z, u0_z));

  BigRat v_x = BigRat::Div(ax.center.x, ax.cert.B);
  BigRat v_y = BigRat::Div(ax.center.y, ax.cert.B);
  BigRat v_z = BigRat::Div(ax.center.z, ax.cert.B);
  BigRat dot_v_u0 = BigRat::Plus(
    BigRat::Plus(BigRat::Times(v_x, u0_x), BigRat::Times(v_y, u0_y)),
    BigRat::Times(v_z, u0_z));

  BigRat lam = BigRat::Div(dot_v_u0, norm_u0_sq);
  BigRat w_x = BigRat::Minus(v_x, BigRat::Times(lam, u0_x));
  BigRat w_y = BigRat::Minus(v_y, BigRat::Times(lam, u0_y));
  BigRat w_z = BigRat::Minus(v_z, BigRat::Times(lam, u0_z));

  BigRat dot_w_u0 = BigRat::Plus(
    BigRat::Plus(BigRat::Times(w_x, u0_x), BigRat::Times(w_y, u0_y)),
    BigRat::Times(w_z, u0_z));
  std::cout << "Exact dot(w, u0) == 0: " << BigRat::IsZero(dot_w_u0) << "\n";

  BigRat norm_w_sq = BigRat::Plus(
    BigRat::Plus(BigRat::Times(w_x, w_x), BigRat::Times(w_y, w_y)),
    BigRat::Times(w_z, w_z));
  BigRat c_cone(35, 1000);
  BigRat c_core(55, 100000);

  BigRat c_cone_sq = BigRat::Times(c_cone, c_cone);
  BigRat LHS = BigRat::Times(norm_w_sq, BigRat::Minus(norm_u0_sq, c_cone_sq));
  BigRat margin = BigRat::Minus(BigRat::Times(lam, c_cone), c_core);
  BigRat margin_sq = BigRat::Times(margin, margin);
  BigRat RHS = BigRat::Times(norm_u0_sq, margin_sq);

  std::cout << "margin >= 0: " << BigRat::GreaterEq(margin, BigRat(0)) << "\n";
  std::cout << "Exact hineq (LHS <= RHS): " << BigRat::LessEq(LHS, RHS) << "\n";
  std::cout << "lam = " << lam.ToString() << "\n";
  std::cout << "w.x = " << w_x.ToString() << "\n";
  std::cout << "w.y = " << w_y.ToString() << "\n";
  std::cout << "w.z = " << w_z.ToString() << "\n";

  return 0;
}
