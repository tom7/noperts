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

  std::string err;
  double min_defect = 1e9;
  int best_m0 = -1, best_m1 = -1, best_m2 = -1;

  for (int m0 = 600; m0 <= 1000; m0 += 50) {
    for (int m1 = 600; m1 <= 1000; m1 += 50) {
      for (int m2 = 0; m2 <= 1000; m2 += 25) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(13, 14, 14, 15, m2, 14)
        };
        AxisCertificate ax;
        BigVecQ3 ctr;
        BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
          double d = del.ToDouble();
          if (d < min_defect) {
            min_defect = d;
            best_m0 = m0; best_m1 = m1; best_m2 = m2;
            std::cout << "New min defect: " << min_defect << " at m0=" << m0 << ", m1=" << m1 << ", m2=" << m2 << "\n";
          }
        }
      }
    }
  }

  std::cout << "Best defect: " << min_defect << " at (" << best_m0 << ", " << best_m1 << ", " << best_m2 << ")\n";
  return 0;
}
