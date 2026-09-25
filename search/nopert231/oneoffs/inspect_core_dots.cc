#include <iostream>
#include <iomanip>
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
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = yocto::length(u0);
  vec3 u0_hat = u0 / norm_u0;

  ContactInfo core_contacts[7][3] = {
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 800, 15}, {3, 2, 2, 1, 0, 2}},
    {{2, 1, 1, 4, 0, 1}, {1, 4, 4, 8, 0, 4}, {15, 19, 19, 3, 500, 19}},
    {{2, 1, 1, 4, 0, 1}, {4, 8, 8, 9, 800, 8}, {15, 19, 19, 3, 500, 19}},
    {{2, 1, 1, 4, 666, 1}, {1, 4, 4, 8, 800, 4}, {10, 15, 15, 19, 200, 15}},
    {{2, 1, 1, 4, 800, 1}, {1, 4, 4, 8, 1000, 4}, {10, 15, 15, 19, 333, 15}},
    {{3, 2, 2, 1, 0, 2}, {1, 4, 4, 8, 666, 4}, {10, 15, 15, 19, 333, 15}},
    {{3, 2, 2, 1, 0, 2}, {1, 4, 4, 8, 800, 4}, {10, 15, 15, 19, 333, 15}}
  };

  vec3 v[7];
  for (int m = 0; m < 7; m++) {
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    Tube229::AuditAxis(tri, core_contacts[m], &cert, &ctr, &del, &err, BigRat(1, 1000));
    v[m] = vec3{ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
    std::cout << "v[" << m << "] . u0_hat = " << yocto::dot(v[m], u0_hat) << "\n";
  }

  return 0;
}
