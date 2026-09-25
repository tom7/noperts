#include <iostream>
#include <vector>
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

  ContactInfo cont_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 c_core;
  BigRat d_core;
  std::string err;
  Tube229::AuditAxis(tri, cont_core, &ax_core, &c_core, &d_core, &err, BigRat(0));

  vec3 u_core = {c_core.x.ToDouble(), c_core.y.ToDouble(), c_core.z.ToDouble()};
  std::cout << "u_core: (" << u_core.x << ", " << u_core.y << ", " << u_core.z << ")\n";
  std::cout << "len(u_core) = " << yocto::length(u_core) << "\n";

  // The linear displacement rate for axis a is a · u_core!
  // It is positive if and only if a · u_core > 0!
  // Which is a HEMISPHERE centered at u_core!

  return 0;
}
