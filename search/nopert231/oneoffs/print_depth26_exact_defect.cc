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

  BigRat max_def(0);
  for (int p = 1; p <= 10000000; p = (p == 0 ? 1 : p * 10)) {
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    if (Tube229::AuditAxis(tri, c0, &ax, &ctr, &del, &err, BigRat(1, p))) {
      std::cout << "Audits with max_allowed_defect = 1/" << p << "!\n";
      break;
    }
  }
  return 0;
}
