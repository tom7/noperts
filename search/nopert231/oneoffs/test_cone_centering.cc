#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0));
  vec3 v0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "v0: (" << v0.x << ", " << v0.y << ", " << v0.z << ")\n";
  vec3 neg_v0 = -v0;
  std::cout << "-v0: (" << neg_v0.x << ", " << neg_v0.y << ", " << neg_v0.z << ")\n";

  // Let's inspect the current complement axes:
  ContactInfo base_c[4][3] = {
    {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}},
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  AxisCertificate ax[4]; BigVecQ3 ctr[4]; BigRat del[4];
  for (int j = 0; j < 4; j++) Tube229::AuditAxis(tri, base_c[j], &ax[j], &ctr[j], &del[j], &err, BigRat(0));
  vec3 v[4];
  for (int j = 0; j < 4; j++) {
    double B = ax[j].B.ToDouble();
    v[j] = vec3{ctr[j].x.ToDouble() / B, ctr[j].y.ToDouble() / B, ctr[j].z.ToDouble() / B};
  }

  // Solve W * u = -v0, where W = [v1, v2, v3]
  double W[3][4] = {
    {v[1].x, v[2].x, v[3].x, -v0.x},
    {v[1].y, v[2].y, v[3].y, -v0.y},
    {v[1].z, v[2].z, v[3].z, -v0.z}
  };
  for (int col = 0; col < 3; col++) {
    int pivot = col;
    for (int r = col + 1; r < 3; r++) if (std::abs(W[r][col]) > std::abs(W[pivot][col])) pivot = r;
    for (int c_idx = 0; c_idx <= 3; c_idx++) std::swap(W[col][c_idx], W[pivot][c_idx]);
    for (int r = col + 1; r < 3; r++) {
      double factor = W[r][col] / W[col][col];
      for (int c_idx = col; c_idx <= 3; c_idx++) W[r][c_idx] -= factor * W[col][c_idx];
    }
  }
  double u[3];
  for (int r = 2; r >= 0; r--) {
    u[r] = W[r][3];
    for (int c_idx = r + 1; c_idx < 3; c_idx++) u[r] -= W[r][c_idx] * u[c_idx];
    u[r] /= W[r][r];
  }
  std::cout << "Current u = -W^{-1} v0: (" << u[0] << ", " << u[1] << ", " << u[2] << ")\n";

  return 0;
}
