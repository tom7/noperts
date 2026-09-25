#include <iostream>
#include <vector>
#include <cmath>
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
    // ax0:
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14) },
    // ax1:
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(2, 1, 1, 4, 333, 1) },
    // ax2:
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 666, 15), MakeContact(3, 2, 2, 1, 0, 2) },
    // ax3:
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(1, 4, 4, 8, 333, 4), MakeContact(15, 19, 19, 3, 1000, 19) }
  };

  BigVecQ3 ctr[4]; BigRat B[4]; BigRat del[4]; std::string err;
  for (int j = 0; j < 4; j++) {
    AxisCertificate ax;
    bool ok = Tube229::AuditAxis(tri, cts[j], &ax, &ctr[j], &del[j], &err, BigRat(5, 1000));
    std::cout << "j=" << j << " ok=" << ok << " err=" << err << "\n";
    B[j] = ax.B;
  }

  return 0;
}
