#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  
  std::cout << "u0 unnormalized: (" << ctr0.x.ToDouble() / ax0.B.ToDouble() << ", "
            << ctr0.y.ToDouble() / ax0.B.ToDouble() << ", "
            << ctr0.z.ToDouble() / ax0.B.ToDouble() << ")\n";
  std::cout << "u0 rational: (" << (ctr0.x / ax0.B).ToString() << ", "
            << (ctr0.y / ax0.B).ToString() << ", "
            << (ctr0.z / ax0.B).ToString() << ")\n";

  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.z.ToDouble() / ax0.B.ToDouble()});
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.z.ToDouble() / ax0.B.ToDouble()});
  std::cout << "u0 unit: (" << u0.x << ", " << u0.y << ", " << u0.z << "), norm_u0 = " << norm_u0 << "\n";

  return 0;
}
