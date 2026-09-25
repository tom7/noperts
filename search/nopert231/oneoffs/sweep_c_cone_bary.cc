#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

BigRat Det4(const BigRat m[4][4]) {
  BigRat a = m[0][0], b = m[0][1], c = m[0][2], d = m[0][3];
  BigRat e = m[1][0], f = m[1][1], g = m[1][2], h = m[1][3];
  BigRat i = m[2][0], j = m[2][1], k = m[2][2], l = m[2][3];
  BigRat n = m[3][0], o = m[3][1], p = m[3][2], q = m[3][3];

  BigRat kp_lo = k * q - l * p;
  BigRat jp_ln = j * q - l * o;
  BigRat jo_kn = j * p - k * o;
  BigRat ip_lm = i * q - l * n;
  BigRat io_km = i * p - k * n;
  BigRat in_jm = i * o - j * n;

  BigRat d1 = f * kp_lo - g * jp_ln + h * jo_kn;
  BigRat d2 = e * kp_lo - g * ip_lm + h * io_km;
  BigRat d3 = e * jp_ln - f * ip_lm + h * in_jm;
  BigRat d4 = e * jo_kn - f * io_km + g * in_jm;

  return a * d1 - b * d2 + c * d3 - d * d4;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));

  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int cage_idx[3] = {0, 24, 210};
  BigVecQ3 u[4];
  u[0] = {ann_center.x / ann_cert.B, ann_center.y / ann_cert.B, ann_center.z / ann_cert.B};
  for (int m = 0; m < 3; m++) {
    const auto &ax = axes[cage_idx[m]];
    u[m + 1] = {ax.center.x / ax.cert.B, ax.center.y / ax.cert.B, ax.center.z / ax.cert.B};
  }

  BigRat delta = BigRat(234013, 1000000000);

  for (double c_cone_d : {0.015, 0.020, 0.025, 0.030, 0.035, 0.040, 0.045, 0.050}) {
    BigRat c_cone = BigRat((int)(c_cone_d * 1000), 1000);
    double best_min_l = -1;
    double best_c = -1;
    for (int c_int = 5; c_int <= 35; c_int++) {
      BigRat c = BigRat(c_int, 10000);
      BigRat s = (c + delta) / c_cone;
      BigVecQ3 p[4];
      p[0] = {s * u[0].x, s * u[0].y, s * u[0].z};
      for (int m = 1; m < 4; m++) p[m] = u[m];

      BigRat det_m[4][4] = {
        {p[0].x, p[1].x, p[2].x, p[3].x},
        {p[0].y, p[1].y, p[2].y, p[3].y},
        {p[0].z, p[1].z, p[2].z, p[3].z},
        {BigRat(1), BigRat(1), BigRat(1), BigRat(1)}
      };
      BigRat D = Det4(det_m);
      if (D <= 0) continue;

      BigRat R = BigRat(7, 4) * (c + delta);
      BigVecQ3 oct[6] = {
        {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
        {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
        {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
      };

      bool all_pos = true;
      double min_l = 1e9;
      for (int k = 0; k < 6; k++) {
        for (int l = 0; l < 4; l++) {
          BigRat b_m[4][4];
          for (int r = 0; r < 4; r++) {
            for (int col = 0; col < 4; col++) {
              if (col == l) {
                b_m[r][col] = (r < 3) ? ((r == 0) ? oct[k].x : ((r == 1) ? oct[k].y : oct[k].z)) : BigRat(1);
              } else {
                b_m[r][col] = det_m[r][col];
              }
            }
          }
          BigRat l_val = Det4(b_m) / D;
          if (l_val <= 0) { all_pos = false; break; }
          if (l_val.ToDouble() < min_l) min_l = l_val.ToDouble();
        }
        if (!all_pos) break;
      }
      if (all_pos && min_l > best_min_l) {
        best_min_l = min_l;
        best_c = c.ToDouble();
      }
    }
    std::cout << "c_cone = " << c_cone_d << ": best c = " << best_c << ", min_l = " << best_min_l << "\n";
  }
  return 0;
}
