#include <iostream>
#include <vector>
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

  for (int m = 0; m <= 300; m += 20) {
    ContactInfo core_c[3] = {
      MakeContact(3, 2, 2, 1, 150, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(10, 15, 15, 19, m, 15)
    };
    AxisCertificate core_ax;
    BigVecQ3 core_ctr;
    BigRat core_del;
    std::string err;
    bool ok = Tube229::AuditAxis(tri, core_c, &core_ax, &core_ctr, &core_del, &err, BigRat(0));
    std::cout << "m=" << m << ": " << (ok ? "OK" : "FAIL (" + err + ")") << "\n";
  }
  return 0;
}
