#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo new_c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {8, 9, 9, 10, 0, 9}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, new_c0, &ax0, &ctr0, &del0, &err, BigRat(0));

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  int i = 165;
  ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
  AxisCertificate ax_c; BigVecQ3 ctr_c; BigRat del_c;
  Tube229::AuditAxis(tri, cts, &ax_c, &ctr_c, &del_c, &err, BigRat(0));

  std::cout << "Axis 165 contacts:\n";
  for (int m = 0; m < 3; m++) {
    std::cout << "  MakeContact(" << cts[m].edge_start << ", " << cts[m].edge_finish
              << ", " << cts[m].edge_start2 << ", " << cts[m].edge_finish2
              << ", " << cts[m].mix << ", " << cts[m].vertex << "),\n";
  }
  std::cout << "B = " << ax_c.B.ToDouble() << ", delta = " << del_c.ToDouble() << "\n";

  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigVecQ3 uc = {ctr_c.x / ax_c.B, ctr_c.y / ax_c.B, ctr_c.z / ax_c.B};

  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
  BigRat uc_sq = uc.x * uc.x + uc.y * uc.y + uc.z * uc.z;

  double cos_t = dot.ToDouble() / std::sqrt(u0_sq.ToDouble() * uc_sq.ToDouble());
  double theta = std::acos(cos_t) * 180.0 / M_PI;
  std::cout << "Angle theta: " << theta << " deg\n";
  std::cout << "||u0||: " << std::sqrt(u0_sq.ToDouble()) << "\n";
  std::cout << "||u0|| * sin(theta): " << std::sqrt(u0_sq.ToDouble()) * std::sin(theta * M_PI / 180.0) << "\n";
  std::cout << "4/7 * ||u0||: " << (4.0 / 7.0) * std::sqrt(u0_sq.ToDouble()) << "\n";

  BigRat lam = dot / u0_sq;
  BigVecQ3 w = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
  std::cout << "lam: " << lam.ToDouble() << "\n";
  std::cout << "w: (" << w.x.ToDouble() << ", " << w.y.ToDouble() << ", " << w.z.ToDouble() << ")\n";
  return 0;
}
