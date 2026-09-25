#include <iostream>
#include <vector>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate core_axis;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_axis, &core_center, &core_delta, &err, BigRat(0));

  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  AxisCertificate ax1;
  BigVecQ3 ctr1;
  BigRat del1;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));

  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax2;
  BigVecQ3 ctr2;
  BigRat del2;
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));

  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax3;
  BigVecQ3 ctr3;
  BigRat del3;
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  BigVecQ3 u_ann = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigVecQ3 u_core = {core_center.x / core_axis.B, core_center.y / core_axis.B, core_center.z / core_axis.B};

  BigRat u_ann_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  BigRat dot_ann_core = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
  BigRat lam = dot_ann_core / u_ann_sq;
  BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};
  BigRat w_sq = w.x * w.x + w.y * w.y + w.z * w.z;

  std::cout << "lam = " << lam.ToString() << " (" << lam.ToDouble() << ")\n";
  std::cout << "w.x = " << w.x.ToString() << "\n";
  std::cout << "w.y = " << w.y.ToString() << "\n";
  std::cout << "w.z = " << w.z.ToString() << "\n";
  std::cout << "|w| = " << std::sqrt(w_sq.ToDouble()) << ", |u_ann| = " << std::sqrt(u_ann_sq.ToDouble()) << "\n";

  BigRat delta = std::max({del0, del1, del2, del3, core_delta});
  std::cout << "delta = " << delta.ToString() << " (" << delta.ToDouble() << ")\n";

  BigRat c_cone(28, 1000);
  BigRat box_c(2133147, 1000000000);
  BigRat c_core(2133147, 1000000000);

  // Check barycentric:
  BigRat s = (box_c + delta) / c_cone;
  BigVecQ3 v0 = {u_ann.x * s, u_ann.y * s, u_ann.z * s};
  BigVecQ3 u1 = {ctr1.x / ax1.B, ctr1.y / ax1.B, ctr1.z / ax1.B};
  BigVecQ3 u2 = {ctr2.x / ax2.B, ctr2.y / ax2.B, ctr2.z / ax2.B};
  BigVecQ3 u3 = {ctr3.x / ax3.B, ctr3.y / ax3.B, ctr3.z / ax3.B};

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

  bool bary_ok = true;
  for (int k = 0; k < 6; k++) {
    BigVecQ3 p = target_oct[k];
    BigVecQ3 dp = {p.x - v0.x, p.y - v0.y, p.z - v0.z};
    BigRat l1 = BigVecQ3::Dot(dp, c23) / det;
    BigVecQ3 cpd3 = BigVecQ3::Cross(dp, d3);
    BigRat l2 = BigVecQ3::Dot(d1, cpd3) / det;
    BigVecQ3 cd2p = BigVecQ3::Cross(d2, dp);
    BigRat l3 = BigVecQ3::Dot(d1, cd2p) / det;
    BigRat l0 = BigRat(1) - l1 - l2 - l3;
    std::cout << "k=" << k << ": (" << l0.ToDouble() << ", " << l1.ToDouble() << ", " << l2.ToDouble() << ", " << l3.ToDouble() << ")\n";
    if (l0 < 0 || l1 < 0 || l2 < 0 || l3 < 0) bary_ok = false;
  }
  std::cout << "bary: " << (bary_ok ? "PASS" : "FAIL") << "\n";

  return 0;
}
