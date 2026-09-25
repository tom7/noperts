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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo cts[4][3] = {
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14) },
    { MakeContact(3, 2, 2, 1, 600, 2), MakeContact(1, 4, 4, 8, 600, 4), MakeContact(13, 14, 14, 15, 800, 14) },
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 400, 4), MakeContact(13, 14, 14, 15, 800, 14) },
    { MakeContact(3, 2, 2, 1, 600, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 600, 14) }
  };

  BigVecQ3 ctr[4]; BigRat B[4]; BigRat del[4]; std::string err;
  for (int j = 0; j < 4; j++) {
    AxisCertificate ax;
    Tube229::AuditAxis(tri, cts[j], &ax, &ctr[j], &del[j], &err, j == 0 ? BigRat(5, 1000) : BigRat(0));
    B[j] = ax.B;
    std::cout << "j=" << j << " B=" << B[j].ToString() << " ctr=(" << ctr[j].x.ToString() << ", " << ctr[j].y.ToString() << ", " << ctr[j].z.ToString() << ")\n";
  }
  return 0;
}
