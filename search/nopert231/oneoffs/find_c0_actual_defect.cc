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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;

  for (int d = 0; d <= 1000; d++) {
    BigRat test_D(d, 100000000); // 1e-8
    if (Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, test_D)) {
      std::cout << "c0 audit succeeded with D = " << test_D.ToDouble()
                << " (" << test_D.ToString() << "), delta = " << del0.ToDouble() << "\n";
      break;
    }
  }
  return 0;
}
