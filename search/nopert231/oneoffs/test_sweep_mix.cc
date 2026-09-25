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
  std::string path = "03121303022";
  TriangleQ tri = TriangleFromPath(path);

  BigRat min_defect(1);
  int best_mix = -1;

  for (int mix = 150; mix <= 250; mix++) {
    ContactInfo c0[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(13, 14, 14, 15, mix, 14)
    };
    AxisCertificate ax0;
    BigVecQ3 center0;
    BigRat delta0;
    std::string err;
    if (Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(1, 100))) {
      BigRat D0 = Tube229::ComputeSupportDefect(tri, c0);
      std::cout << "mix=" << mix << " D0=" << D0.ToDouble() << "\n";
      if (D0 < min_defect) {
        min_defect = D0;
        best_mix = mix;
      }
    }
  }

  std::cout << "Best mix: " << best_mix << " min D0=" << min_defect.ToDouble() << "\n";
  return 0;
}
