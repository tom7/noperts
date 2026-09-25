#include <iostream>
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
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_zero[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };

  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  bool ok = Tube229::AuditAxis(tri, c_zero, &ax0, &ctr0, &del0, &err, BigRat(0));
  std::cout << "AuditAxis with ZERO defect on 03121300: " << (ok ? "SUCCESS!" : "FAILED: " + err) << "\n";
  if (ok) {
    std::cout << "del0 = " << del0.ToString() << " (" << del0.ToDouble() << ")\n";
    std::cout << "B0 = " << ax0.B.ToString() << " (" << ax0.B.ToDouble() << ")\n";
    std::cout << "center = (" << ctr0.x.ToDouble() << ", " << ctr0.y.ToDouble() << ", " << ctr0.z.ToDouble() << ")\n";
  }
  return 0;
}
