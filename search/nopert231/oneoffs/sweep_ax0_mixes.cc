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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  std::cout << "Sweeping mixes for ax0 contacts...\n";
  int found_zero = 0;
  double min_defect = 1.0;

  for (int m0 = 100; m0 <= 900; m0 += 100) {
    for (int m1 = 100; m1 <= 900; m1 += 100) {
      for (int m2 = 100; m2 <= 900; m2 += 100) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(13, 14, 14, 15, m2, 14)
        };
        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        std::string err;
        if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(1, 100))) {
          double d = del.ToDouble();
          if (d < min_defect) min_defect = d;
          if (d <= 0.0) {
            found_zero++;
            std::cout << "FOUND ZERO DEFECT: m=(" << m0 << ", " << m1 << ", " << m2 << ")!\n";
          }
        }
      }
    }
  }

  std::cout << "Min defect found: " << min_defect << ", zero-defect count: " << found_zero << "\n";
  return 0;
}
