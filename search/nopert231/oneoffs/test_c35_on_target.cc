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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c35[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax35; BigVecQ3 ctr35; BigRat del35; std::string err;
  bool ok = Tube229::AuditAxis(tri, c35, &ax35, &ctr35, &del35, &err, BigRat(0));
  std::cout << "ok = " << ok << ", err = " << err << "\n";
  std::cout << "del35 = " << del35.ToDouble() << "\n";
  std::cout << "B = " << ax35.B.ToDouble() << "\n";
  return 0;
}
