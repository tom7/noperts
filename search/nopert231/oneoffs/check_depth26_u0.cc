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
  std::string target = "03121300211212201212122222";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  AxisCertificate ax;
  BigVecQ3 ctr;
  BigRat del;
  std::string err;
  if (Tube229::AuditAxis(tri, c0, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
    double len = sqrt((ctr.x * ctr.x + ctr.y * ctr.y + ctr.z * ctr.z).ToDouble());
    std::cout << "Depth 26: u0 length = " << len << ", delta = " << del.ToDouble() << "\n";
    std::cout << "Max c_cone = (4/7) * len = " << (4.0 / 7.0) * len << "\n";
  } else {
    std::cout << "AuditAxis failed: " << err << "\n";
  }
  return 0;
}
