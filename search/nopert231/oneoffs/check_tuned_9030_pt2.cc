#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = std::sqrt(yocto::dot(u0, u0));
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double x = 0.945;
  double y = 1.085;
  vec3 a = yocto::normalize(x * k1 + y * k2 + e3);

  ContactInfo info9030[3] = {axes[9030].cert.contacts[0], axes[9030].cert.contacts[1], axes[9030].cert.contacts[2]};
  info9030[0].mix = 600; info9030[1].mix = 0; info9030[2].mix = 1000;
  AxisCertificate cert9030;
  BigVecQ3 ctr9030;
  BigRat del9030;
  std::string err9030;
  Tube229::AuditAxis(tri, info9030, &cert9030, &ctr9030, &del9030, &err9030, BigRat(1, 1000));
  double B = cert9030.B.ToDouble();
  vec3 v = vec3{ctr9030.x.ToDouble() / B, ctr9030.y.ToDouble() / B, ctr9030.z.ToDouble() / B};
  double d = yocto::dot(a, v);

  std::cout << "Tuned 9030: delta = " << del9030.ToDouble() << ", dot = " << d << "\n";

  return 0;
}
