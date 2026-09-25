#include <iostream>
#include <iomanip>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Compute triangle center and corner distance (box.c)
  BigVecQ3 center = (tri.corners[0] + tri.corners[1] + tri.corners[2]) / BigRat(3);
  BigRat c_sq(0);
  for (int i = 0; i < 3; i++) {
    BigVecQ3 diff = tri.corners[i] - center;
    BigRat d2 = diff.x * diff.x + diff.y * diff.y + diff.z * diff.z;
    if (d2 > c_sq) c_sq = d2;
  }
  std::cout << "Triangle max corner distance squared = " << c_sq.ToString()
            << " (sqrt = " << std::sqrt(c_sq.ToDouble()) << ")\n";

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  std::cout << "ax0.B = " << ax0.B.ToString() << " (" << ax0.B.ToDouble() << ")\n";
  std::cout << "del0 = " << del0.ToString() << " (" << del0.ToDouble() << ")\n";
  std::cout << "del0 / B = " << (del0.ToDouble() / ax0.B.ToDouble()) << "\n";

  return 0;
}
