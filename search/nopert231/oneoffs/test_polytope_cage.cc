#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  double norm_u0 = std::sqrt((u0.x * u0.x + u0.y * u0.y + u0.z * u0.z).ToDouble());

  // We want c_cone such that the inner disk angle psi <= 51.72 deg
  // cos(51.72 deg) * norm_u0
  double c_cone_disk = std::cos(51.72 * M_PI / 180.0) * norm_u0;
  std::cout << "norm_u0 = " << norm_u0 << "\n";
  std::cout << "c_cone_disk = " << c_cone_disk << " (psi = 51.72 deg)\n";

  // Let's test if p0 and some complement axes can cage the octahedron!
  // In Lean:
  // p0 = ((c + delta) / c_cone) * u0
  // Target octahedron vertices: +- (7/4)*(c + delta) * e_i
  // Dividing by (c + delta):
  // p0' = (1 / c_cone) * u0
  // Octahedron vertices: +- 1.75 * e_i (i = 0, 1, 2)
  // Complement axes: each audited axis has center u_j = ctr_j / B_j
  // For u_j, its variation bound certifies margin c:
  // In Lean's single_complement_axis:
  // inner a u_j >= c + delta => inner a v_real >= c.

  vec3 p0_prime = {u0.x.ToDouble() / c_cone_disk, u0.y.ToDouble() / c_cone_disk, u0.z.ToDouble() / c_cone_disk};
  std::cout << "||p0'|| = " << yocto::length(p0_prime) << " (need >= 1.75)\n";

  return 0;
}
