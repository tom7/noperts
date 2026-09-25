#include <iostream>
#include <vector>
#include <iomanip>
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

  int m[12] = {
    150, 1000, 882,
    50, 800, 950,
    1000, 1000, 343,
    113, 320, 150
  };

  ContactInfo c[4][3] = {
    { MakeContact(3, 2, 2, 1, m[0], 2),
      MakeContact(1, 4, 4, 8, m[1], 4),
      MakeContact(13, 14, 14, 15, m[2], 14) },
    { MakeContact(2, 1, 1, 4, m[3], 1),
      MakeContact(10, 15, 15, 19, m[4], 15),
      MakeContact(19, 3, 3, 2, m[5], 3) },
    { MakeContact(2, 1, 1, 4, m[6], 1),
      MakeContact(8, 9, 9, 10, m[7], 9),
      MakeContact(9, 10, 10, 15, m[8], 10) },
    { MakeContact(3, 2, 2, 1, m[9], 2),
      MakeContact(1, 4, 4, 8, m[10], 4),
      MakeContact(10, 15, 15, 19, m[11], 15) }
  };

  std::string err;
  AxisCertificate ax[4];
  BigVecQ3 cnt[4];
  BigRat del[4];
  for (int a = 0; a < 4; a++) {
    Tube229::AuditAxis(tri, c[a], &ax[a], &cnt[a], &del[a], &err, BigRat(1, 1000));
  }

  BigRat delta(234013, 1000000000);

  for (double c_cone_d : {0.015, 0.020, 0.025, 0.030, 0.035}) {
    BigRat c_cone(std::round(c_cone_d * 10000), 10000);
    for (double box_c_d : {0.0001, 0.0002, 0.0005, 0.001, 0.002, 0.005, 0.010}) {
      BigRat box_c(std::round(box_c_d * 100000), 100000);
      BigRat scale_0 = (box_c + delta) / c_cone;
      BigVecQ3 v[4];
      v[0] = {cnt[0].x * scale_0, cnt[0].y * scale_0, cnt[0].z * scale_0};
      for (int a = 1; a < 4; a++) v[a] = cnt[a];

      BigVecQ3 d0 = v[0] - v[3];
      BigVecQ3 d1 = v[1] - v[3];
      BigVecQ3 d2 = v[2] - v[3];
      BigRat det = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, d2));

      BigRat R = BigRat(7, 4) * (box_c + delta);
      BigVecQ3 oct[6] = {
        {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
        {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
        {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
      };

      BigRat min_l(100);
      for (int o = 0; o < 6; o++) {
        BigVecQ3 dp = oct[o] - v[3];
        BigRat l0 = BigVecQ3::Dot(dp, BigVecQ3::Cross(d1, d2)) / det;
        BigRat l1 = BigVecQ3::Dot(d0, BigVecQ3::Cross(dp, d2)) / det;
        BigRat l2 = BigVecQ3::Dot(d0, BigVecQ3::Cross(d1, dp)) / det;
        BigRat l3 = BigRat(1) - l0 - l1 - l2;
        for (int coord = 0; coord < 4; coord++) {
          BigRat val = (coord == 0 ? l0 : coord == 1 ? l1 : coord == 2 ? l2 : l3);
          if (val < min_l) min_l = val;
        }
      }
      if (min_l > 0) {
        std::cout << "VALID: c_cone=" << c_cone_d << ", box_c=" << box_c_d << " -> min_l=" << min_l.ToDouble() << "\n";
      }
    }
  }
  return 0;
}
