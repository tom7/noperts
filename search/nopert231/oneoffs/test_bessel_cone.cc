#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static BigRat DotQ(const BigVecQ3 &a, const BigVecQ3 &b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  auto &ax = axes[3063];
  ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
  AxisCertificate cert; BigVecQ3 ctr; BigRat del;
  Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));

  BigVecQ3 u = ctr0;
  BigVecQ3 v = ctr;
  BigRat u_dot_u = DotQ(u, u);
  BigRat v_dot_u = DotQ(v, u);
  BigRat lam = v_dot_u / u_dot_u;
  BigVecQ3 w = {v.x - lam * u.x, v.y - lam * u.y, v.z - lam * u.z};
  BigRat w_dot_w = DotQ(w, w);

  std::cout << "lam = " << lam.ToDouble() << "\n";
  std::cout << "|u| = " << std::sqrt(u_dot_u.ToDouble()) << "\n";
  std::cout << "|w| = " << std::sqrt(w_dot_w.ToDouble()) << "\n";

  BigRat c_core(1, 1000);
  for (int c_int = 15; c_int <= 70; c_int++) {
    BigRat c_cone(c_int, 1000);
    BigRat lhs = w_dot_w * (u_dot_u - c_cone * c_cone);
    BigRat rhs = u_dot_u * (lam * c_cone - c_core) * (lam * c_cone - c_core);
    bool ok = (lam * c_cone >= c_core) && (lhs <= rhs);
    double u_len = std::sqrt(u_dot_u.ToDouble());
    double cos_psi = c_cone.ToDouble() / u_len;
    double psi_deg = (cos_psi <= 1.0) ? std::acos(cos_psi) * 180.0 / M_PI : 0.0;
    if (ok) {
      std::cout << "c_cone = " << c_int << "/1000 (psi = " << psi_deg << " deg): OK! margin = "
                << (rhs - lhs).ToDouble() << "\n";
    }
  }
  return 0;
}
