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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  std::string err;
  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 ctr0, ctr1, ctr2, ctr3;
  BigRat del0, del1, del2, del3;

  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  BigRat delta = del0;
  BigRat c_cone(24, 1000);

  BigVecQ3 u1 = {ctr1.x / ax1.B, ctr1.y / ax1.B, ctr1.z / ax1.B};
  BigVecQ3 u2 = {ctr2.x / ax2.B, ctr2.y / ax2.B, ctr2.z / ax2.B};
  BigVecQ3 u3 = {ctr3.x / ax3.B, ctr3.y / ax3.B, ctr3.z / ax3.B};

  for (int denom : {2000, 3000, 4000, 5000, 6000, 8000, 10000, 15000, 20000, 30000}) {
    BigRat box_c(1, denom);
    BigRat s = (box_c + delta) / c_cone;
    BigVecQ3 v0 = {ctr0.x * s / ax0.B, ctr0.y * s / ax0.B, ctr0.z * s / ax0.B};

    BigVecQ3 target_oct[6] = {
      {BigRat(7, 4) * (box_c + delta), BigRat(0), BigRat(0)},
      {-BigRat(7, 4) * (box_c + delta), BigRat(0), BigRat(0)},
      {BigRat(0), BigRat(7, 4) * (box_c + delta), BigRat(0)},
      {BigRat(0), -BigRat(7, 4) * (box_c + delta), BigRat(0)},
      {BigRat(0), BigRat(0), BigRat(7, 4) * (box_c + delta)},
      {BigRat(0), BigRat(0), -BigRat(7, 4) * (box_c + delta)}
    };

    BigVecQ3 d1 = {u1.x - v0.x, u1.y - v0.y, u1.z - v0.z};
    BigVecQ3 d2 = {u2.x - v0.x, u2.y - v0.y, u2.z - v0.z};
    BigVecQ3 d3 = {u3.x - v0.x, u3.y - v0.y, u3.z - v0.z};
    BigVecQ3 c23 = {d2.y * d3.z - d2.z * d3.y, d2.z * d3.x - d2.x * d3.z, d2.x * d3.y - d2.y * d3.x};
    BigRat det = d1.x * c23.x + d1.y * c23.y + d1.z * c23.z;

    bool all_valid = true;
    for (int k = 0; k < 6; k++) {
      BigVecQ3 p = target_oct[k];
      BigVecQ3 dp = {p.x - v0.x, p.y - v0.y, p.z - v0.z};
      BigRat l1 = (dp.x * c23.x + dp.y * c23.y + dp.z * c23.z) / det;
      BigVecQ3 cpd3 = {dp.y * d3.z - dp.z * d3.y, dp.z * d3.x - dp.x * d3.z, dp.x * d3.y - dp.y * d3.x};
      BigRat l2 = (d1.x * cpd3.x + d1.y * cpd3.y + d1.z * cpd3.z) / det;
      BigVecQ3 cd2p = {d2.y * dp.z - d2.z * dp.y, d2.z * dp.x - d2.x * dp.z, d2.x * dp.y - d2.y * dp.x};
      BigRat l3 = (d1.x * cd2p.x + d1.y * cd2p.y + d1.z * cd2p.z) / det;
      BigRat l0 = BigRat(1) - l1 - l2 - l3;
      if (l0 < 0 || l1 < 0 || l2 < 0 || l3 < 0) {
        all_valid = false;
        break;
      }
    }
    if (denom == 4000) {
      for (int k = 0; k < 6; k++) {
        BigVecQ3 p = target_oct[k];
        BigVecQ3 dp = {p.x - v0.x, p.y - v0.y, p.z - v0.z};
        BigRat l1 = (dp.x * c23.x + dp.y * c23.y + dp.z * c23.z) / det;
        BigVecQ3 cpd3 = {dp.y * d3.z - dp.z * d3.y, dp.z * d3.x - dp.x * d3.z, dp.x * d3.y - dp.y * d3.x};
        BigRat l2 = (d1.x * cpd3.x + d1.y * cpd3.y + d1.z * cpd3.z) / det;
        BigVecQ3 cd2p = {d2.y * dp.z - d2.z * dp.y, d2.z * dp.x - d2.x * dp.z, d2.x * dp.y - d2.y * dp.x};
        BigRat l3 = (d1.x * cd2p.x + d1.y * cd2p.y + d1.z * cd2p.z) / det;
        BigRat l0 = BigRat(1) - l1 - l2 - l3;
        std::cout << "k=" << k << ": (" << l0.ToDouble() << ", " << l1.ToDouble() << ", " << l2.ToDouble() << ", " << l3.ToDouble() << ")\n";
      }
    }
  }

  return 0;
}
