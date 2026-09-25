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
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  // 5 flock axes:
  int flock_idx[5] = {3064, 174, 3054, 4911, 4924};
  vec3 v[5];
  for (int m = 0; m < 5; m++) {
    int idx = flock_idx[m];
    ContactInfo cts[3] = {axes[idx].cert.contacts[0], axes[idx].cert.contacts[1], axes[idx].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v[m] = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    std::cout << "Axis " << m << ": dot(v, u0) = " << yocto::dot(v[m], u0)
              << ", dot(v, k1) = " << yocto::dot(v[m], k1)
              << ", dot(v, k2) = " << yocto::dot(v[m], k2) << "\n";
  }

  return 0;
}
