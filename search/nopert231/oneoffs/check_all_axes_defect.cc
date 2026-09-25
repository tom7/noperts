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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  int m[12] = {
    150, 1000, 882,
    50, 800, 950,
    1000, 1000, 343,
    113, 320, 150
  };

  ContactInfo c[4][3] = {
    { MakeContact(3, 2, 2, 1, m[0], 2),
      MakeContact(1, 4, 4, 8, m[1], 4),
      MakeContact(13, 14, 14, 15, m[2], 14) },
    { MakeContact(2, 1, 1, 4, m[3], 1),
      MakeContact(10, 15, 15, 19, m[4], 15),
      MakeContact(19, 3, 3, 2, m[5], 3) },
    { MakeContact(2, 1, 1, 4, m[6], 1),
      MakeContact(8, 9, 9, 10, m[7], 9),
      MakeContact(9, 10, 10, 15, m[8], 10) },
    { MakeContact(3, 2, 2, 1, m[9], 2),
      MakeContact(1, 4, 4, 8, m[10], 4),
      MakeContact(10, 15, 15, 19, m[11], 15) }
  };

  std::cout << "Testing zero-defect audit (BigRat(0)) on all 4 axes:\n";
  for (int a = 0; a < 4; a++) {
    std::string err;
    AxisCertificate ax;
    BigVecQ3 cnt;
    BigRat var_radius;
    bool ok = Tube229::AuditAxis(tri, c[a], &ax, &cnt, &var_radius, &err, BigRat(0));
    std::cout << "Axis " << a << ": Audit = " << (ok ? "OK" : "FAIL (" + err + ")") << "\n";
  }

  return 0;
}
