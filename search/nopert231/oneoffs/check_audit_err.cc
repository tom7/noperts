#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start; c.edge_finish2 = finish;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo triple0[3] = {
    MakeContact(19, 3, 1000, 3),
    MakeContact(3, 2, 1000, 2),
    MakeContact(2, 1, 1000, 1)
  };

  AxisCertificate ax0;
  BigVecQ3 cQ0;
  BigRat delta0;
  std::string err;

  bool ok = Tube229::AuditAxis(tri, triple0, &ax0, &cQ0, &delta0, &err, BigRat(1, 10000));
  std::cout << "Audit result: " << ok << ", err: " << err << "\n";
  return 0;
}
