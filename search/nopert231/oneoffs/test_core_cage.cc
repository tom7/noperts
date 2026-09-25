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

  // Core axis:
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  // Comp 0:
  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  // Comp 1:
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  // Comp 2:
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  ContactInfo *contacts[4] = {c_core, c1, c2, c3};
  BigVecQ3 tet[4];
  std::string err;
  for (int a = 0; a < 4; a++) {
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    Tube229::AuditAxis(tri, contacts[a], &ax, &center, &delta, &err, BigRat(0));
    tet[a] = center / ax.B;
    std::cout << "Axis " << a << ": (" << tet[a].x.ToDouble() << ", "
              << tet[a].y.ToDouble() << ", " << tet[a].z.ToDouble() << ")\n";
  }

  BigRat inrad = Tube229::ExactTetrahedronAxisRadius(tet);
  std::cout << "Exact inradius of {v_core, comp0, comp1, comp2}: " << inrad.ToDouble()
            << " (" << inrad.ToString() << ")\n";

  return 0;
}
