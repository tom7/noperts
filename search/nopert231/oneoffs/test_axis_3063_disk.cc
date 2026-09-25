#include <iostream>
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
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  int idx = 3063;
  auto &ax = axes[idx];
  ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
  AxisCertificate cert; BigVecQ3 ctr; BigRat del;
  Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
  vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});

  double dot_u0_v = yocto::dot(u0_f, v);
  double angle_u0_v = std::acos(dot_u0_v) * 180.0 / M_PI;
  std::cout << "Axis 3063: dot with u0_hat = " << dot_u0_v << ", angle = " << angle_u0_v << " deg\n";

  // For any point a on S^2 at angle psi from u0_hat:
  // dot(a, v) >= cos(psi + angle_u0_v)
  // For dot(a, v) >= 0.005:
  // psi + angle_u0_v <= acos(0.005) = 89.71 deg
  // psi <= 89.71 - 32.68 = 57.03 deg!
  double max_psi = std::acos(0.005) * 180.0 / M_PI - angle_u0_v;
  std::cout << "Axis 3063 GUARANTEES dot(a, v) >= 0.005 for all a with angle(a, u0_hat) <= " << max_psi << " deg!\n";

  double c_cone = 0.015;
  double alpha = std::acos(c_cone / std::sqrt((u0.x*u0.x + u0.y*u0.y + u0.z*u0.z).ToDouble())) * 180.0 / M_PI;
  std::cout << "The entire exceptional cone has half-angle alpha = " << alpha << " deg\n";
  std::cout << "So Axis 3063 covers the entire inner disk [0, 57.03 deg] of the " << alpha << " deg cone!\n";

  return 0;
}
