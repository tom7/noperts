#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo base_c[4][3] = {
    {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}},
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  AxisCertificate ax[4]; BigVecQ3 ctr[4]; BigRat del[4]; std::string err;
  for (int j = 0; j < 4; j++) Tube229::AuditAxis(tri, base_c[j], &ax[j], &ctr[j], &del[j], &err, BigRat(0));
  vec3 v[4];
  for (int j = 0; j < 4; j++) {
    double B = ax[j].B.ToDouble();
    v[j] = vec3{ctr[j].x.ToDouble() / B, ctr[j].y.ToDouble() / B, ctr[j].z.ToDouble() / B};
  }

  double delta = 0.000260;
  double c_cone = 0.025;
  double c_margin = 0.000265;
  double scale0 = (c_margin + delta) / c_cone;
  vec3 dec_v[4] = {v[0] * scale0, v[1], v[2], v[3]};

  // Solve for origin barycentric coordinates:
  double A[4][5] = {
    {dec_v[0].x, dec_v[1].x, dec_v[2].x, dec_v[3].x, 0.0},
    {dec_v[0].y, dec_v[1].y, dec_v[2].y, dec_v[3].y, 0.0},
    {dec_v[0].z, dec_v[1].z, dec_v[2].z, dec_v[3].z, 0.0},
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
  std::cout << "Origin b: (" << b[0] << ", " << b[1] << ", " << b[2] << ", " << b[3] << ")\n";

  return 0;
}
