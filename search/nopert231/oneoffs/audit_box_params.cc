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

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  int b1 = 0, b2 = 24, b3 = 210;
  const auto &ax1 = axes[b1];
  const auto &ax2 = axes[b2];
  const auto &ax3 = axes[b3];

  BigRat delta = std::max({del0, ax1.delta, ax2.delta, ax3.delta});
  BigRat box_c(3, 1000);
  BigRat c_cone(15, 1000);
  BigRat r(1, 200);
  BigRat r_min(1, 220);

  std::cout << "del0 = " << del0.ToString() << "\n";
  std::cout << "del1 = " << ax1.delta.ToString() << "\n";
  std::cout << "del2 = " << ax2.delta.ToString() << "\n";
  std::cout << "del3 = " << ax3.delta.ToString() << "\n";
  std::cout << "delta = " << delta.ToString() << "\n";

  // Check Barycentric with exact BigRat:
  BigVecQ3 u1 = {ax1.center.x / ax1.cert.B, ax1.center.y / ax1.cert.B, ax1.center.z / ax1.cert.B};
  BigVecQ3 u2 = {ax2.center.x / ax2.cert.B, ax2.center.y / ax2.cert.B, ax2.center.z / ax2.cert.B};
  BigVecQ3 u3 = {ax3.center.x / ax3.cert.B, ax3.center.y / ax3.cert.B, ax3.center.z / ax3.cert.B};
  BigRat s = (box_c + delta) / c_cone;
  BigVecQ3 v0 = {ctr0.x * s / ax0.B, ctr0.y * s / ax0.B, ctr0.z * s / ax0.B};
  BigVecQ3 d1 = {u1.x - v0.x, u1.y - v0.y, u1.z - v0.z};
  BigVecQ3 d2 = {u2.x - v0.x, u2.y - v0.y, u2.z - v0.z};
  BigVecQ3 d3 = {u3.x - v0.x, u3.y - v0.y, u3.z - v0.z};
  BigVecQ3 c23 = BigVecQ3::Cross(d2, d3);
  BigRat det = BigVecQ3::Dot(d1, c23);

  BigRat R = BigRat(7, 4) * (box_c + delta);
  BigVecQ3 target_oct[6] = {
    {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
  };

  BigRat min_l(100);
  for (int k = 0; k < 6; k++) {
    BigVecQ3 p = target_oct[k];
    BigVecQ3 dp = {p.x - v0.x, p.y - v0.y, p.z - v0.z};
    BigRat l1 = BigVecQ3::Dot(dp, c23) / det;
    BigVecQ3 cpd3 = BigVecQ3::Cross(dp, d3);
    BigRat l2 = BigVecQ3::Dot(d1, cpd3) / det;
    BigVecQ3 cd2p = BigVecQ3::Cross(d2, dp);
    BigRat l3 = BigVecQ3::Dot(d1, cd2p) / det;
    BigRat l0 = BigRat(1) - l1 - l2 - l3;
    min_l = std::min({min_l, l0, l1, l2, l3});
  }
  std::cout << "Exact BigRat min_l = " << min_l.ToString() << " (" << min_l.ToDouble() << ")\n";

  // Check annular dominance:
  BigRat D0("40453116150493257294382818402404626020428339063662464854174529123912781/550830080000000000000000000000000000000000000000000000000000000000000000000");
  BigRat ann_lhs = BigRat(1, 2) * r * r * ax0.B + D0;
  ann_lhs = ann_lhs * ann_lhs;
  BigRat c_cone_eff = c_cone - delta;
  BigRat ann_rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (c_cone_eff * c_cone_eff * ax0.B * ax0.B);
  std::cout << "Annular dominance: lhs=" << ann_lhs.ToDouble() << ", rhs=" << ann_rhs.ToDouble()
            << " -> " << (ann_lhs <= ann_rhs ? "PASS" : "FAIL") << "\n";

  // Check complement angle:
  BigRat c_eff = box_c - delta;
  BigRat comp_lhs = r * r * (BigRat(1) + c_eff * c_eff);
  BigRat comp_rhs = BigRat(4) * c_eff * c_eff;
  std::cout << "Complement angle: lhs=" << comp_lhs.ToDouble() << ", rhs=" << comp_rhs.ToDouble()
            << " -> " << (comp_lhs <= comp_rhs ? "PASS" : "FAIL") << "\n";

  return 0;
}
