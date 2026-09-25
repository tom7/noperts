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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat var0;
  bool ok = Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &var0, &err, BigRat(0));
  std::cout << "Audit with max_allowed_defect = 0: " << (ok ? "SUCCESS" : "FAIL") << "\n";
  if (!ok) std::cout << "Error: " << err << "\n";
  return 0;
}
