#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 100, 2},
    {1, 4, 4, 8, 0, 4},
    {13, 14, 14, 15, 1000, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  const auto &ax1 = axes[23];
  const auto &ax2 = axes[24];
  const auto &ax3 = axes[210];

  double B0 = ax0.B.ToDouble();
  double B1 = ax1.cert.B.ToDouble();
  double B2 = ax2.cert.B.ToDouble();
  double B3 = ax3.cert.B.ToDouble();

  vec3 v0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  vec3 v1 = vec3{ax1.center.x.ToDouble() / B1, ax1.center.y.ToDouble() / B1, ax1.center.z.ToDouble() / B1};
  vec3 v2 = vec3{ax2.center.x.ToDouble() / B2, ax2.center.y.ToDouble() / B2, ax2.center.z.ToDouble() / B2};
  vec3 v3 = vec3{ax3.center.x.ToDouble() / B3, ax3.center.y.ToDouble() / B3, ax3.center.z.ToDouble() / B3};

  double c_cone = 0.017;
  // Check if target points (±c_cone, 0, 0), (0, ±c_cone, 0), (0, 0, ±c_cone) are inside the tetrahedron formed by v0, v1, v2, v3
  // Barycentric coordinates: [v0 v1 v2 v3; 1 1 1 1] * lambda = [p; 1]
  double M[4][4] = {
    {v0.x, v1.x, v2.x, v3.x},
    {v0.y, v1.y, v2.y, v3.y},
    {v0.z, v1.z, v2.z, v3.z},
    {1.0,  1.0,  1.0,  1.0}
  };

  // Invert M
  double invM[4][4];
  // Using 4x4 determinant/inverse
  // Let's solve M * x = p for each of the 6 vertices
  vec3 targets[6] = {
    {c_cone, 0, 0}, {-c_cone, 0, 0},
    {0, c_cone, 0}, {0, -c_cone, 0},
    {0, 0, c_cone}, {0, 0, -c_cone}
  };

  // Gaussian elimination solver:
  auto solve = [&](vec3 p, double lam[4]) -> bool {
    double A[4][5];
    for (int r = 0; r < 4; r++) {
      for (int c = 0; c < 4; c++) A[r][c] = M[r][c];
    }
    A[0][4] = p.x; A[1][4] = p.y; A[2][4] = p.z; A[3][4] = 1.0;

    for (int col = 0; col < 4; col++) {
      int pivot = col;
      for (int r = col + 1; r < 4; r++) {
        if (std::abs(A[r][col]) > std::abs(A[pivot][col])) pivot = r;
      }
      if (std::abs(A[pivot][col]) < 1e-12) return false;
      for (int c = 0; c < 5; c++) std::swap(A[col][c], A[pivot][c]);
      double div = A[col][col];
      for (int c = 0; c < 5; c++) A[col][c] /= div;
      for (int r = 0; r < 4; r++) {
        if (r != col) {
          double factor = A[r][col];
          for (int c = 0; c < 5; c++) A[r][c] -= factor * A[col][c];
        }
      }
    }
    for (int r = 0; r < 4; r++) lam[r] = A[r][4];
    return true;
  };

  bool all_valid = true;
  for (int t = 0; t < 6; t++) {
    double lam[4];
    if (!solve(targets[t], lam)) {
      std::cout << "Singular matrix!\n";
      return 1;
    }
    std::cout << "Target " << t << ": lambda = ("
              << lam[0] << ", " << lam[1] << ", " << lam[2] << ", " << lam[3] << ")\n";
    for (int i = 0; i < 4; i++) {
      if (lam[i] <= 0) all_valid = false;
    }
  }

  if (all_valid) {
    std::cout << "BARYCENTRIC CIRCUMSCRIPTION HOLDS FOR NEW C0!\n";
  } else {
    std::cout << "Barycentric circumscription failed!\n";
  }

  return 0;
}
