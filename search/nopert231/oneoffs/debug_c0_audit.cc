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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };

  std::string err;
  AxisCertificate ax;
  BigVecQ3 cnt;
  BigRat delta;

  bool ok = Tube229::AuditAxis(tri, c0, &ax, &cnt, &delta, &err, BigRat(0));
  std::cout << "AuditAxis ok: " << ok << ", err: " << err << "\n";
  std::cout << "B = " << ax.B.ToDouble() << ", delta = " << delta.ToDouble() << "\n";
  std::cout << "ratio = " << (delta.ToDouble() / ax.B.ToDouble()) << " vs 0.000234013\n";
  return 0;
}
