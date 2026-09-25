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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  AxisCertificate ax1; BigVecQ3 ctr1; BigRat del1;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(5, 1000));

  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax2; BigVecQ3 ctr2; BigRat del2;
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(5, 1000));

  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax3; BigVecQ3 ctr3; BigRat del3;
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(5, 1000));

  ContactInfo c_core[3] = {
    MakeContact(15, 19, 19, 3, 900, 19),
    MakeContact(3, 2, 2, 1, 333, 2),
    MakeContact(4, 8, 8, 9, 1000, 8)
  };
  AxisCertificate ax_core; BigVecQ3 ctr_core; BigRat del_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

  std::cout << "del0 = " << del0.ToString() << " (" << del0.ToDouble() << ")\n";
  std::cout << "del1 = " << del1.ToString() << " (" << del1.ToDouble() << ")\n";
  std::cout << "del2 = " << del2.ToString() << " (" << del2.ToDouble() << ")\n";
  std::cout << "del3 = " << del3.ToString() << " (" << del3.ToDouble() << ")\n";
  std::cout << "del_core = " << del_core.ToString() << " (" << del_core.ToDouble() << ")\n";

  BigRat max_del = del0;
  if (del1 > max_del) max_del = del1;
  if (del2 > max_del) max_del = del2;
  if (del3 > max_del) max_del = del3;
  if (del_core > max_del) max_del = del_core;
  std::cout << "max_del = " << max_del.ToString() << " (" << max_del.ToDouble() << ")\n";

  return 0;
}
