#include <iostream>
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

  ContactInfo c[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(8, 9, 9, 10, 0, 9)
  };
  AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
  bool ok = Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0));
  std::cout << "AuditAxis with defect 0: " << (ok ? "SUCCESS" : "FAILED") << "\n";
  if (!ok) std::cout << "Error: " << err << "\n";
  else {
    vec3 u = {ctr.x.ToDouble() / ax.B.ToDouble(),
              ctr.y.ToDouble() / ax.B.ToDouble(),
              ctr.z.ToDouble() / ax.B.ToDouble()};
    std::cout << "u0: (" << u.x << ", " << u.y << ", " << u.z << "), ||u0|| = " << yocto::length(u)
              << ", B = " << ax.B.ToDouble() << ", delta = " << del.ToDouble() << "\n";
  }
  return 0;
}
