#include <iostream>
#include <vector>
#include <cmath>
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
  for (int m0 = 700; m0 <= 900; m0 += 20) {
    for (int m1 = 700; m1 <= 900; m1 += 20) {
      for (int m2 = 100; m2 <= 400; m2 += 20) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(13, 14, 14, 15, m2, 14)
        };
        AxisCertificate ax;
        BigVecQ3 ctr;
        BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0))) {
          std::cout << "FOUND ZERO-DEFECT c0 mix! m0=" << m0 << ", m1=" << m1 << ", m2=" << m2 << "\n";
          return 0;
        }
      }
    }
  }

  std::cout << "No zero-defect mix with exact contact topology\n";
  return 0;
}
