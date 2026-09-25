#include <iostream>
#include <vector>
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

  int idxs[3] = {3063, 22, 24};
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 v[3];
  for (int i = 0; i < 3; i++) {
    auto &ax = axes[idxs[i]];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v[i] = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
  }

  std::cout << "dot(u0, v[0]): " << yocto::dot(u0, v[0]) << "\n";
  std::cout << "dot(u0, v[1]): " << yocto::dot(u0, v[1]) << "\n";
  std::cout << "dot(u0, v[2]): " << yocto::dot(u0, v[2]) << "\n";
  std::cout << "dot(v[0], v[1]): " << yocto::dot(v[0], v[1]) << "\n";
  std::cout << "dot(v[0], v[2]): " << yocto::dot(v[0], v[2]) << "\n";
  std::cout << "dot(v[1], v[2]): " << yocto::dot(v[1], v[2]) << "\n";

  return 0;
}
