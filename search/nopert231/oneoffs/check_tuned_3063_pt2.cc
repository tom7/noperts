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

  ContactInfo info3063[3] = {axes[3063].cert.contacts[0], axes[3063].cert.contacts[1], axes[3063].cert.contacts[2]};
  info3063[0].mix = 0; info3063[1].mix = 0; info3063[2].mix = 600;
  AxisCertificate cert3063;
  BigVecQ3 ctr3063;
  BigRat del3063;
  std::string err3063;
  Tube229::AuditAxis(tri, info3063, &cert3063, &ctr3063, &del3063, &err3063, BigRat(1, 1000));
  double B = cert3063.B.ToDouble();
  vec3 v = vec3{ctr3063.x.ToDouble() / B, ctr3063.y.ToDouble() / B, ctr3063.z.ToDouble() / B};
  double d = yocto::dot(a, v);

  std::cout << "Tuned 3063: delta = " << del3063.ToDouble() << ", dot = " << d << "\n";

  return 0;
}
