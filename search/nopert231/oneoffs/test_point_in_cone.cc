#include <iostream>
#include <iomanip>
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
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double X = 18.6877, Y = -23.5388;
  vec3 p = P0 + X * E1 + Y * E2;
  vec3 a = yocto::normalize(p);

  double dot_u0 = yocto::dot(a, u0);
  double c_cone = 0.020;

  std::cout << std::setprecision(10);
  std::cout << "At (" << X << ", " << Y << "):\n";
  std::cout << "dot(a, u0) = " << dot_u0 << "\n";
  std::cout << "c_cone     = " << c_cone << "\n";
  std::cout << "Is in cone: " << (dot_u0 >= c_cone ? "YES" : "NO") << "\n";
  return 0;
}
