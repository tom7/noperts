#include <iostream>
#include <vector>
#include <iomanip>
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
    MakeContact(3, 2, 2, 1, 160, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 859, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat dlt0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &dlt0, &err, BigRat(5, 1000));

  BigRat B0 = ax0.B;
  BigRat D0 = dlt0;
  BigRat c_c(278, 10000);

  BigRat r_min(0, 1);
  BigRat r(0, 1);
  bool ok = Tube229::CheckAnnularDominance(B0, D0, c_c, dlt0, &r_min, &r);
  std::cout << "Tube229::CheckAnnularDominance (auto): " << (ok ? "TRUE" : "FALSE") << "\n";
  std::cout << "B0 = " << B0.ToDouble() << "\n";
  std::cout << "D0 = " << D0.ToDouble() << "\n";
  std::cout << "dlt0 = " << dlt0.ToDouble() << "\n";
  std::cout << "c_c = " << c_c.ToDouble() << "\n";
  std::cout << "r_min = " << r_min.ToDouble() << ", r = " << r.ToDouble() << "\n";
  return 0;
}
