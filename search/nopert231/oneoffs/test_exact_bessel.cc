#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

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
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigRat u0_sq = u0.x*u0.x + u0.y*u0.y + u0.z*u0.z;

  auto &ax = axes[3063];
  ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
  AxisCertificate cert; BigVecQ3 ctr; BigRat del;
  Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
  BigVecQ3 v = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
  BigRat v_sq = v.x*v.x + v.y*v.y + v.z*v.z;

  // We want to test with normalized v, or v_hat.
  // In Lean, v_hat has ||v_hat|| = 1.
  // Let lambda = (v . u0) / u0_sq.
  BigRat dot_vu = v.x*u0.x + v.y*u0.y + v.z*u0.z;
  // Let's compute lambda and ||w||^2 for v_hat:
  // (v_hat . u0) = dot_vu / sqrt(v_sq)
  // But wait, inner_covers_of_ortho_projection works with ANY v!
  // If v is NOT normalized, inner(a, v) >= c2.
  // Then inner(a, v / ||v||) >= c2 / ||v||.
  // Or we can choose an exact rational unit-like vector v0!
  // What is ||v||?
  std::cout << "v_sq = " << v_sq.ToDouble() << ", sqrt(v_sq) = " << std::sqrt(v_sq.ToDouble()) << "\n";
  std::cout << "u0_sq = " << u0_sq.ToDouble() << ", ||u0|| = " << std::sqrt(u0_sq.ToDouble()) << "\n";

  // Let's test with rational c1:
  // c1 / ||u0|| = cos(psi). If psi = 51.5 deg, cos(psi) = 0.6225.
  // c1 = 0.6225 * 0.0511116 = 0.031817. Let c1 = 318 / 10000.
  BigRat c1(318, 10000);
  std::cout << "c1 = " << c1.ToDouble() << ", c1 / ||u0|| = " << c1.ToDouble() / std::sqrt(u0_sq.ToDouble()) << "\n";

  // lambda = (v . u0) / u0_sq
  BigRat lambda = dot_vu / u0_sq;
  BigVecQ3 w = {v.x - lambda * u0.x, v.y - lambda * u0.y, v.z - lambda * u0.z};
  BigRat w_sq = w.x*w.x + w.y*w.y + w.z*w.z;

  std::cout << "lambda = " << lambda.ToDouble() << "\n";
  std::cout << "w_sq = " << w_sq.ToDouble() << "\n";

  // Test c2 = 1 / 1000 * sqrt(v_sq) = 0.001 * 0.0518 = 0.0000518:
  for (int c2_num : {1, 2, 5, 10, 20}) {
    BigRat c2(c2_num, 100000);
    BigRat lhs = w_sq * (u0_sq - c1*c1);
    BigRat rhs = u0_sq * (lambda * c1 - c2) * (lambda * c1 - c2);
    std::cout << "c2 = " << c2.ToDouble() << ": lhs = " << lhs.ToDouble() << ", rhs = " << rhs.ToDouble()
              << ", margin (rhs - lhs) = " << (rhs - lhs).ToDouble() << "\n";
  }

  return 0;
}
