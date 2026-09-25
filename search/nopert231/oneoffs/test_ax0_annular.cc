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
  BigRat max_def(5, 1000);
  bool ok = Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &var0, &err, max_def);
  std::cout << "Audit ok: " << ok << "\n";

  BigRat B0 = ax0.B;
  BigRat c_cone(278, 10000);
  BigRat delta(234013, 1000000000);
  BigRat r_min(1, 10000);
  BigRat r(1, 2000);

  BigRat D(15, 100000); // 0.00015
  bool ann_ok = Tube229::CheckAnnularDominance(B0, D, c_cone, delta, &r_min, &r);
  std::cout << "CheckAnnularDominance with D=0.00015: " << ann_ok << "\n";

  for (int d = 1; d <= 20; d++) {
    BigRat test_D(d, 100000);
    bool res = Tube229::CheckAnnularDominance(B0, test_D, c_cone, delta, &r_min, &r);
    std::cout << "  D = " << test_D.ToDouble() << ": " << res << "\n";
  }
  return 0;
}
