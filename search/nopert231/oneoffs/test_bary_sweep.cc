#include <iostream>
#include <vector>
#include <cmath>
#include "bignum/big-overloads.h"
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  // Cage axes: 0, 23, 24, 210
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  ContactInfo c1[3] = {
    {2, 1, 1, 4, 0, 1},
    {10, 15, 15, 19, 500, 15},
    {3, 2, 2, 1, 0, 2}
  };
  ContactInfo c2[3] = {
    {2, 1, 1, 4, 0, 1},
    {10, 15, 15, 19, 666, 15},
    {3, 2, 2, 1, 0, 2}
  };
  ContactInfo c3[3] = {
    {2, 1, 1, 4, 0, 1},
    {1, 4, 4, 8, 333, 4},
    {15, 19, 19, 3, 1000, 19}
  };

  AxisCertificate ax[4];
  BigVecQ3 ctr[4];
  BigRat del[4];
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax[0], &ctr[0], &del[0], &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c1, &ax[1], &ctr[1], &del[1], &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c2, &ax[2], &ctr[2], &del[2], &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c3, &ax[3], &ctr[3], &del[3], &err, BigRat(1, 1000));

  BigRat c_margin(1, 1000);
  BigRat delta(165, 1000000);

  // In Lean, decomposedCenter c_cone 0 = ((c + delta)/c_cone) * v0
  // and decomposedCenter c_cone j = vj for j in {1, 2, 3}.
  // decomposedBarycentricValid tests if the 6 octahedron vertices are in the conical hull of {v0', v1, v2, v3}
  // with positive weights.
  // Let us sweep c_cone from 15/1000 to 30/1000!

  for (int c_num = 15; c_num <= 35; c_num++) {
    BigRat c_cone(c_num, 1000);
    BigRat scale = (c_margin + delta) / c_cone;
    BigVecQ3 v0_prime = ctr[0] * (scale / ax[0].B);
    BigVecQ3 v[4];
    v[0] = v0_prime;
    v[1] = ctr[1] * (BigRat(1) / ax[1].B);
    v[2] = ctr[2] * (BigRat(1) / ax[2].B);
    v[3] = ctr[3] * (BigRat(1) / ax[3].B);

    // Compute determinant
    // [v1 - v0, v2 - v0, v3 - v0]
    BigVecQ3 d1 = v[1] - v[0];
    BigVecQ3 d2 = v[2] - v[0];
    BigVecQ3 d3 = v[3] - v[0];
    BigRat det = d1.x * (d2.y * d3.z - d2.z * d3.y) -
                 d1.y * (d2.x * d3.z - d2.z * d3.x) +
                 d1.z * (d2.x * d3.y - d2.y * d3.x);

    // Check barycentric coordinates for all 6 octahedron vertices
    bool ok = (det > BigRat(0));
    BigVecQ3 oct[6] = {
      {BigRat(1), BigRat(0), BigRat(0)}, {BigRat(-1), BigRat(0), BigRat(0)},
      {BigRat(0), BigRat(1), BigRat(0)}, {BigRat(0), BigRat(-1), BigRat(0)},
      {BigRat(0), BigRat(0), BigRat(1)}, {BigRat(0), BigRat(0), BigRat(-1)}
    };

    // For conical hull, check if each oct[k] can be written as sum_{j=0}^3 lambda_j v[j] with lambda_j >= 0
    // i.e., M * lambda = oct[k], solve 3x3 system with 4 rays?
    // Wait, in Lean: Box.decomposedBarycentricValid:
    // It takes 4 tetrahedral subsets or the full conical hull?
    std::cout << "c_cone = " << c_num << "/1000: det = " << det.ToDouble() << "\n";
  }

  return 0;
}
