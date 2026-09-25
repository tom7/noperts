#include <iostream>
#include <vector>
#include <cmath>
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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Loaded " << axes.size() << " hull support axes\n";

  std::cout << "Loaded " << axes.size() << " hull support axes (all zero defect)\n";

  // Test if any of these zero-defect axes can be u0 with complement axes from the set
  // We want:
  // p0 = ((c + delta) / c_cone) * u0
  // p1, p2, p3 = u1, u2, u3
  // such that det > 0 and all 6 octahedron vertices have barycentric > 0
  BigRat delta = BigRat(234013, 1000000000);
  BigRat c = BigRat(15, 10000);
  BigRat c_cone = BigRat(15, 1000);
  BigRat s = (c + delta) / c_cone;
  BigRat R = BigRat(7, 4) * (c + delta);
  BigVecQ3 oct[6] = {
    {R, BigRat(0), BigRat(0)}, {-R, BigRat(0), BigRat(0)},
    {BigRat(0), R, BigRat(0)}, {BigRat(0), -R, BigRat(0)},
    {BigRat(0), BigRat(0), R}, {BigRat(0), BigRat(0), -R}
  };

  // Complement axes from earlier cage:
  int comp_idx[3] = {0, 24, 210};
  BigVecQ3 p[4];
  for (int m = 0; m < 3; m++) {
    const auto &ax = axes[comp_idx[m]];
    p[m + 1] = {ax.center.x / ax.cert.B, ax.center.y / ax.cert.B, ax.center.z / ax.cert.B};
  }

  int success_count = 0;
  for (size_t idx = 0; idx < axes.size(); idx++) {
    const auto &ax0 = axes[idx];
    BigVecQ3 u0 = {ax0.center.x / ax0.cert.B, ax0.center.y / ax0.cert.B, ax0.center.z / ax0.cert.B};
    p[0] = {s * u0.x, s * u0.y, s * u0.z};

    BigRat det_m[4][4] = {
      {p[0].x, p[1].x, p[2].x, p[3].x},
      {p[0].y, p[1].y, p[2].y, p[3].y},
      {p[0].z, p[1].z, p[2].z, p[3].z},
      {BigRat(1), BigRat(1), BigRat(1), BigRat(1)}
    };
    BigRat D = Det4(det_m);
    if (D <= 0) continue;

    bool all_pos = true;
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
        if (Det4(b_m) / D <= 0) { all_pos = false; break; }
      }
      if (!all_pos) break;
    }
    if (all_pos) {
      success_count++;
      std::cout << "FOUND ZERO-DEFECT u0! axis idx = " << idx
                << ", B = " << ax0.cert.B.ToString()
                << ", center = (" << u0.x.ToDouble() << ", " << u0.y.ToDouble() << ", " << u0.z.ToDouble() << ")\n";
      if (success_count >= 5) break;
    }
  }

  std::cout << "Total zero-defect u0 found: " << success_count << "\n";
  return 0;
}
