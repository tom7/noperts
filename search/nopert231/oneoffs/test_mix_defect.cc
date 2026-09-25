#include <iostream>
#include <vector>
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

  for (int mix = 0; mix <= 1000; mix += 50) {
    ContactInfo c[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(13, 14, 14, 15, mix, 14)
    };

    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &center, &delta, &err, BigRat(0))) {
      std::cout << "mix = " << mix << ": ZERO DEFECT!\n";
    } else {
      std::cout << "mix = " << mix << ": fail (" << err << ")\n";
    }
  }
  return 0;
}
