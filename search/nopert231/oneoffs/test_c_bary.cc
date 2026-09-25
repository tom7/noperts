#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c[4][3] = {
    {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}},
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };

  AxisCertificate ax[4]; BigVecQ3 ctr[4]; BigRat del[4]; std::string err;
  for (int j = 0; j < 4; j++) {
    Tube229::AuditAxis(tri, c[j], &ax[j], &ctr[j], &del[j], &err, BigRat(0));
  }

  vec3 v[4];
  for (int j = 0; j < 4; j++) {
    double B = ax[j].B.ToDouble();
    v[j] = vec3{ctr[j].x.ToDouble() / B, ctr[j].y.ToDouble() / B, ctr[j].z.ToDouble() / B};
  }

  double delta = 0.000260;
  double c_cone = 0.025;

  for (double c_margin : {0.000260, 0.000265, 0.000280, 0.000285, 0.000290, 0.000300, 0.000320, 0.000350}) {
    double scale0 = (c_margin + delta) / c_cone;
    vec3 dec_v[4] = {v[0] * scale0, v[1], v[2], v[3]};
    double rad = (c_margin + delta) * 1.75;
    vec3 targets[6] = {
      {rad, 0, 0}, {-rad, 0, 0},
      {0, rad, 0}, {0, -rad, 0},
      {0, 0, rad}, {0, 0, -rad}
    };

    double min_b = 1e9;
    for (int k = 0; k < 6; k++) {
      double A[4][5] = {
        {dec_v[0].x, dec_v[1].x, dec_v[2].x, dec_v[3].x, targets[k].x},
        {dec_v[0].y, dec_v[1].y, dec_v[2].y, dec_v[3].y, targets[k].y},
        {dec_v[0].z, dec_v[1].z, dec_v[2].z, dec_v[3].z, targets[k].z},
        {1.0, 1.0, 1.0, 1.0, 1.0}
      };
      for (int col = 0; col < 4; col++) {
        int pivot = col;
        for (int r = col + 1; r < 4; r++) if (std::abs(A[r][col]) > std::abs(A[pivot][col])) pivot = r;
        for (int c_idx = 0; c_idx <= 4; c_idx++) std::swap(A[col][c_idx], A[pivot][c_idx]);
        for (int r = col + 1; r < 4; r++) {
          double factor = A[r][col] / A[col][col];
          for (int c_idx = col; c_idx <= 4; c_idx++) A[r][c_idx] -= factor * A[col][c_idx];
        }
      }
      double b[4];
      for (int r = 3; r >= 0; r--) {
        b[r] = A[r][4];
        for (int c_idx = r + 1; c_idx < 4; c_idx++) b[r] -= A[r][c_idx] * b[c_idx];
        b[r] /= A[r][r];
      }
      for (int i = 0; i < 4; i++) min_b = std::min(min_b, b[i]);
    }
    std::cout << "c_margin = " << c_margin << " (c = " << c_margin * 1e6 << "/1e6): min_b = " << min_b << "\n";
  }

  return 0;
}
