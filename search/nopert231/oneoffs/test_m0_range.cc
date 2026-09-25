#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

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
  std::string err;

  for (int m = 350; m <= 500; m += 5) {
    ContactInfo c0[3] = {
      MakeContact(3, 2, 2, 1, 280, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(14, 15, 15, 19, m, 15)
    };
    AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
    bool ok = Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0));
    std::cout << "m0_2 = " << m << ": ok = " << ok << "\n";
  }
  return 0;
}
