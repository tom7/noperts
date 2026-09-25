#include <iostream>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  vec3 axis = yocto::normalize(-u0);
  vec3 perp1 = yocto::normalize(yocto::cross(axis, vec3{1, 0, 0}));
  if (yocto::length(yocto::cross(axis, vec3{1, 0, 0})) < 0.1) {
    perp1 = yocto::normalize(yocto::cross(axis, vec3{0, 1, 0}));
  }
  vec3 perp2 = yocto::cross(axis, perp1);

  double rad = 84.0 * M_PI / 180.0;
  double ca = std::cos(rad);
  double sa = std::sin(rad);

  vec3 ideal1 = yocto::normalize(axis * ca + perp1 * sa);
  vec3 ideal2 = yocto::normalize(axis * ca + (perp1 * (-0.5) + perp2 * (std::sqrt(3.0)/2.0)) * sa);
  vec3 ideal3 = yocto::normalize(axis * ca + (perp1 * (-0.5) - perp2 * (std::sqrt(3.0)/2.0)) * sa);

  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  std::cout << "ideal1: (" << ideal1.x << ", " << ideal1.y << ", " << ideal1.z << ")\n";
  std::cout << "ideal2: (" << ideal2.x << ", " << ideal2.y << ", " << ideal2.z << ")\n";
  std::cout << "ideal3: (" << ideal3.x << ", " << ideal3.y << ", " << ideal3.z << ")\n";

  return 0;
}
