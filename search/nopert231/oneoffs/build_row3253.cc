#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"
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
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  std::cout << "del0 = " << del0.ToString() << " (" << del0.ToDouble() << ")\n";

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  int b1 = 0, b2 = 24, b3 = 210;
  const auto &ax1 = axes[b1];
  const auto &ax2 = axes[b2];
  const auto &ax3 = axes[b3];

  ContactInfo core_contacts[3] = {
    MakeContact(14, 15, 15, 19, 300, 15),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 500, 15)
  };
  AxisCertificate core_axis;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_axis, &core_center, &core_delta, &err, BigRat(0));
  std::cout << "core_delta = " << core_delta.ToDouble() << "\n";


  BigVecQ3 u_ann = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigVecQ3 u_core = {core_center.x / core_axis.B, core_center.y / core_axis.B, core_center.z / core_axis.B};

  BigRat u_ann_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  BigRat dot_ann_core = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
  BigRat lam = dot_ann_core / u_ann_sq;
  BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};
  BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

  std::cout << "lam = " << lam.ToDouble() << ", |w| = " << std::sqrt(w_sq.ToDouble()) << ", |u_ann| = " << std::sqrt(u_ann_sq.ToDouble()) << "\n";
  std::cout << "dot(u_ann, u_core)/(|u_ann|*|u_core|) = " << (dot_ann_core.ToDouble() / (std::sqrt(u_ann_sq.ToDouble()) * std::sqrt((u_core.x*u_core.x + u_core.y*u_core.y + u_core.z*u_core.z).ToDouble()))) << "\n";

  BigRat delta = std::max({del0, ax1.delta, ax2.delta, ax3.delta, core_delta});
  BigRat box_c(3, 1000);
  BigRat c_cone(15, 1000);
  BigRat r(1, 200);
  BigRat r_min(1, 220);


  std::cout << "delta = " << delta.ToString() << " (" << delta.ToDouble() << ")\n";
  std::cout << "box_c = " << box_c.ToString() << "\n";
  std::cout << "c_cone = " << c_cone.ToString() << "\n";
  std::cout << "r = " << r.ToString() << "\n";
  std::cout << "r_min = " << r_min.ToString() << "\n";

  // 1. Check box_c >= delta
  bool c_margin_ok = (delta <= box_c);
  std::cout << "1. box.δ <= box.c: " << (c_margin_ok ? "PASS" : "FAIL") << "\n";

  // 2. Check complement angle: r^2 * (1 + (box_c - delta)^2) <= 4 * (box_c - delta)^2
  BigRat c_eff = box_c - delta;
  BigRat comp_lhs = r * r * (BigRat(1) + c_eff * c_eff);
  BigRat comp_rhs = BigRat(4) * c_eff * c_eff;
  std::cout << "2. Complement angle: " << (comp_lhs <= comp_rhs ? "PASS" : "FAIL")
            << " (lhs=" << comp_lhs.ToDouble() << ", rhs=" << comp_rhs.ToDouble() << ")\n";

  // 3. Check annular dominance: ((1/2)*r^2*B0 + D0)^2 <= r_min^2 * (1 - (1/4)*r^2) * ((c_cone - delta)^2 * B0^2)
  BigRat D0("40453116150493257294382818402404626020428339063662464854174529123912781/550830080000000000000000000000000000000000000000000000000000000000000000000");
  BigRat ann_lhs = BigRat(1, 2) * r * r * ax0.B + D0;
  ann_lhs = ann_lhs * ann_lhs;
  BigRat c_cone_eff = c_cone - delta;
  BigRat ann_rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (c_cone_eff * c_cone_eff * ax0.B * ax0.B);
  std::cout << "3. Annular dominance: " << (ann_lhs <= ann_rhs ? "PASS" : "FAIL")
            << " (lhs=" << ann_lhs.ToDouble() << ", rhs=" << ann_rhs.ToDouble() << ")\n";

  BigVecQ3 u1 = {ax1.center.x / ax1.cert.B, ax1.center.y / ax1.cert.B, ax1.center.z / ax1.cert.B};
  BigVecQ3 u2 = {ax2.center.x / ax2.cert.B, ax2.center.y / ax2.cert.B, ax2.center.z / ax2.cert.B};
  BigVecQ3 u3 = {ax3.center.x / ax3.cert.B, ax3.center.y / ax3.cert.B, ax3.center.z / ax3.cert.B};
  BigRat R = BigRat(7, 4) * (box_c + delta);
  BigVecQ3 target_oct[6] = {
    {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
  };

  c_cone = BigRat(30, 1000);
  for (int c_int = 1; c_int <= 15; c_int++) {
    BigRat box_c(c_int, 1000);
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

    std::cout << "box_c=" << box_c.ToDouble() << ": s=" << s.ToDouble() << ", min_l=" << min_l.ToDouble()
              << (min_l > 0 ? " [BARY OK]" : " [bary fail]") << "\n";
  }
  return 0;
}


