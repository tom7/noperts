#include <iostream>
#include <vector>
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
  double min_defect = 100.0;
  int best_m0 = -1, best_m1 = -1, best_m2 = -1;

  for (int m0 = 100; m0 <= 200; m0 += 10) {
    for (int m1 = 900; m1 <= 1000; m1 += 20) {
      for (int m2 = 800; m2 <= 1000; m2 += 10) {
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
            std::cout << "m=(" << m0 << "," << m1 << "," << m2 << "): defect=" << d << "\n";
          }
          if (d <= 0.0) {
            std::cout << "EXACT ZERO DEFECT FOUND at (" << m0 << "," << m1 << "," << m2 << ")!\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Best m=(" << best_m0 << "," << best_m1 << "," << best_m2 << ") with defect = " << min_defect << "\n";
  return 0;
}
