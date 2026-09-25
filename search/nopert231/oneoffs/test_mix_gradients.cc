#include <iostream>
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

static bool SolveTetraOrigin(const BigVecQ3& p0, const BigVecQ3& p1,
                             const BigVecQ3& p2, const BigVecQ3& p3,
                             BigRat w[4]) {
  BigRat M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  BigRat rhs[3] = {-p3.x, -p3.y, -p3.z};

  BigRat det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (det == BigRat(0)) return false;

  BigRat d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  BigRat d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  BigRat d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = BigRat(1) - w[0] - w[1] - w[2];
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Baseline at m0_2 = 395:
  int m0[3] = {280, 1000, 395};
  int m1[3] = {0, 680, 750};
  int m2[3] = {30, 200, 430};
  int m3[3] = {350, 150, 30};

  auto Eval = [&](int m0_[3], int m1_[3], int m2_[3], int m3_[3], double out_w[4]) -> bool {
    ContactInfo c0[3] = {MakeContact(3, 2, 2, 1, m0_[0], 2), MakeContact(1, 4, 4, 8, m0_[1], 4), MakeContact(14, 15, 15, 19, m0_[2], 15)};
    ContactInfo c1[3] = {MakeContact(2, 1, 1, 4, m1_[0], 1), MakeContact(10, 15, 15, 19, m1_[1], 15), MakeContact(19, 3, 3, 2, m1_[2], 3)};
    ContactInfo c2[3] = {MakeContact(19, 3, 3, 2, m2_[0], 3), MakeContact(2, 1, 1, 0, m2_[1], 1), MakeContact(10, 15, 15, 19, m2_[2], 15)};
    ContactInfo c3[3] = {MakeContact(3, 2, 2, 1, m3_[0], 2), MakeContact(8, 9, 9, 10, m3_[1], 9), MakeContact(9, 10, 10, 13, m3_[2], 10)};

    AxisCertificate ax[4]; BigVecQ3 cnt[4]; BigRat del[4];
    if (!Tube229::AuditAxis(tri, c0, &ax[0], &cnt[0], &del[0], &err, BigRat(0))) return false;
    if (!Tube229::AuditAxis(tri, c1, &ax[1], &cnt[1], &del[1], &err, BigRat(0))) return false;
    if (!Tube229::AuditAxis(tri, c2, &ax[2], &cnt[2], &del[2], &err, BigRat(0))) return false;
    if (!Tube229::AuditAxis(tri, c3, &ax[3], &cnt[3], &del[3], &err, BigRat(0))) return false;

    BigRat w[4];
    if (!SolveTetraOrigin(cnt[0]/ax[0].B, cnt[1]/ax[1].B, cnt[2]/ax[2].B, cnt[3]/ax[3].B, w)) return false;
    for (int k = 0; k < 4; k++) out_w[k] = w[k].ToDouble();
    return true;
  };

  double base_w[4];
  Eval(m0, m1, m2, m3, base_w);

  std::cout << "\nTesting m3_1 from 150 down to 0:\n";
  for (int m3_1 = 150; m3_1 >= 0; m3_1 -= 10) {
    int cur_m3[3] = {m3[0], m3_1, m3[2]};
    double new_w[4];
    if (Eval(m0, m1, m2, cur_m3, new_w)) {
      std::cout << "m3_1=" << m3_1
                << ": w0=" << new_w[0] << ", w1=" << new_w[1]
                << ", w2=" << new_w[2] << ", w3=" << new_w[3]
                << " (min_w=" << std::min({new_w[0], new_w[1], new_w[2], new_w[3]}) << ")\n";
    } else {
      std::cout << "m3_1=" << m3_1 << ": Eval failed\n";
    }
  }

  // Test sensitivity dw2, dw3 to each parameter (+10 delta):
  int delta = 10;
  for (int ax = 0; ax < 4; ax++) {
    for (int param = 0; param < 3; param++) {
      int cur_m[4][3] = {{m0[0], m0[1], m0[2]}, {m1[0], m1[1], m1[2]}, {m2[0], m2[1], m2[2]}, {m3[0], m3[1], m3[2]}};
      cur_m[ax][param] += delta;
      double new_w[4];
      if (Eval(cur_m[0], cur_m[1], cur_m[2], cur_m[3], new_w)) {
        double dw2 = (new_w[2] - base_w[2]) / delta;
        double dw3 = (new_w[3] - base_w[3]) / delta;
        std::cout << "Ax" << ax << " p" << param << ": dw2/dm = " << std::setprecision(5) << dw2
                  << ", dw3/dm = " << dw3
                  << " (ratio = " << (dw2 / (dw3 != 0 ? dw3 : 1e-12)) << ")\n";
      }
    }
  }

  return 0;
}
