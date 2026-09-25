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

  std::string err;
  for (int a = 0; a < 4; a++) {
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    Tube229::AuditAxis(tri, c[a], &ax, &ctr, &del, &err, BigRat(1, 1000));
    double len = std::sqrt(ctr.x.ToDouble()*ctr.x.ToDouble() + ctr.y.ToDouble()*ctr.y.ToDouble() + ctr.z.ToDouble()*ctr.z.ToDouble());
    std::cout << "Axis " << a << ": B=" << ax.B.ToDouble() << ", ctr=("
              << ctr.x.ToDouble() << ", " << ctr.y.ToDouble() << ", " << ctr.z.ToDouble()
              << "), norm=" << len << "\n";
  }
  return 0;
}
