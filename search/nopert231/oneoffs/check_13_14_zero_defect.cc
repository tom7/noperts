#include <iostream>
#include <iomanip>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  std::cout << "Testing BigRat(0) defect for Contact 2 on (13,14,14,15) with vertex 14:\n";
  for (int m = 0; m <= 1000; m += 100) {
    ContactInfo c[3] = {
      MakeContact(3, 2, 2, 1, 150, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(13, 14, 14, 15, m, 14)
    };
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    bool ok = Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0));
    std::cout << "m=" << m << ": Audit " << (ok ? "OK" : "FAIL (" + err + ")") << "\n";
  }

  return 0;
}
