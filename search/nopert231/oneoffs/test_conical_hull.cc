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
  BigVecQ3 u0_q = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0 = yocto::normalize(vec3{u0_q.x.ToDouble(), u0_q.y.ToDouble(), u0_q.z.ToDouble()});

  std::vector<int> flock_idx = {3054, 119, 3063, 22, 24};
  std::vector<vec3> v;
  for (int idx : flock_idx) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  for (size_t i = 0; i < v.size(); i++) {
    std::cout << "v[" << i << "] (ax " << flock_idx[i] << "): ("
              << v[i].x << ", " << v[i].y << ", " << v[i].z << ")\n";
  }

  return 0;
}
