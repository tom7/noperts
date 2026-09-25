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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  std::string err;
  AxisCertificate ax;
  BigVecQ3 ctr;
  BigRat del;

  for (int m0 = 750; m0 <= 850; m0 += 10) {
    for (int m1 = 750; m1 <= 850; m1 += 10) {
      for (int m2 = 150; m2 <= 250; m2 += 10) {
        ContactInfo c0[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(13, 14, 14, 15, m2, 14)
        };
        if (Tube229::AuditAxis(tri, c0, &ax, &ctr, &del, &err, BigRat(0))) {
          std::cout << "FOUND ZERO DEFECT AXIS! mixes = (" << m0 << ", " << m1 << ", " << m2
                    << "), delta = " << del.ToDouble() << "\n";
          return 0;
        }
      }
    }
  }
  std::cout << "No zero defect found in grid.\n";
  return 0;
}
