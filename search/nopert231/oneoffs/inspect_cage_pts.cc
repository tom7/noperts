#include <iostream>
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

  ContactInfo contacts[4][3] = {
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(2, 1, 1, 4, 333, 1) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 666, 15), MakeContact(3, 2, 2, 1, 0, 2) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(1, 4, 4, 8, 333, 4), MakeContact(15, 19, 19, 3, 1000, 19) }
  };

  BigVecQ3 ctr[4];
  AxisCertificate ax[4];
  BigRat del[4];
  std::string err;

  for (int j = 0; j < 4; j++) {
    bool ok = Tube229::AuditAxis(tri, contacts[j], &ax[j], &ctr[j], &del[j], &err, BigRat(5, 1000));
    if (!ok) return 1;
    std::cout << "j=" << j << " B=" << ax[j].B.ToDouble() 
              << " ctr=(" << ctr[j].x.ToDouble() << ", " << ctr[j].y.ToDouble() << ", " << ctr[j].z.ToDouble() << ")\n";
  }

  return 0;
}
