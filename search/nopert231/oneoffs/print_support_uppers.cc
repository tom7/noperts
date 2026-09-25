#include <iostream>
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
    MakeContact(3, 2, 2, 1, 200, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 480, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 624, 15),
    MakeContact(3, 2, 2, 1, 0, 2)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 116, 1),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 540, 2),
    MakeContact(8, 9, 9, 10, 200, 9),
    MakeContact(3, 2, 2, 1, 541, 2)
  };

  std::string err;
  AxisCertificate ax[4];
  BigVecQ3 cnt[4];
  BigRat var_radius[4];

  bool ok0 = Tube229::AuditAxis(tri, c0, &ax[0], &cnt[0], &var_radius[0], &err, BigRat(5, 1000));
  bool ok1 = Tube229::AuditAxis(tri, c1, &ax[1], &cnt[1], &var_radius[1], &err, BigRat(5, 1000));
  bool ok2 = Tube229::AuditAxis(tri, c2, &ax[2], &cnt[2], &var_radius[2], &err, BigRat(5, 1000));
  bool ok3 = Tube229::AuditAxis(tri, c3, &ax[3], &cnt[3], &var_radius[3], &err, BigRat(5, 1000));

  std::cout << "Audit results: " << ok0 << ok1 << ok2 << ok3 << "\n";
  for (int a = 0; a < 4; a++) {
    std::cout << "Axis " << a << " B = " << ax[a].B.ToString() << " (" << ax[a].B.ToDouble() << ")\n";
    std::cout << "Axis " << a << " var_radius / B = " << var_radius[a].ToDouble() / ax[a].B.ToDouble() << "\n";
  }

  return 0;
}
