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
  BigVecQ3 u0_q = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0 = {u0_q.x.ToDouble(), u0_q.y.ToDouble(), u0_q.z.ToDouble()};
  vec3 u0_hat = yocto::normalize(u0);

  vec3 ex = yocto::normalize(yocto::cross(u0_hat, std::abs(u0_hat.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_hat, ex);

  auto &ax = axes[3063];
  ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
  AxisCertificate cert; BigVecQ3 ctr; BigRat del;
  Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
  vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});

  for (int k = 18; k <= 23; k++) {
    double phi = k * 15.0 * M_PI / 180.0;
    double d_in = yocto::dot(std::cos(48.0*M_PI/180.0)*u0_hat + std::sin(48.0*M_PI/180.0)*(std::cos(phi)*ex + std::sin(phi)*ey), v);
    double d_out = yocto::dot(std::cos(73.0*M_PI/180.0)*u0_hat + std::sin(73.0*M_PI/180.0)*(std::cos(phi)*ex + std::sin(phi)*ey), v);
    std::cout << "3063 phi " << k * 15 << " deg: in=" << d_in << ", out=" << d_out << "\n";
  }

  return 0;
}
