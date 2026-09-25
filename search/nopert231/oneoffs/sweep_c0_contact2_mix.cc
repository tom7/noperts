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
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);

  for (int m = 0; m <= 1000; m += 50) {
    ContactInfo c[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(13, 14, 14, 15, m, 14)
    };
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0))) {
      std::cout << "mix=" << m << " SUCCESS! del=" << del.ToDouble()
                << " B=" << ax.B.ToDouble() << "\n";
    }
  }
  return 0;
}
