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
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };

  std::string path = "031213002112122012121";
  for (int d = 21; d <= 32; d++) {
    TriangleQ tri = TriangleFromPath(path);
    // Find the exact maximum support value across all 20 vertices and all 3 contacts:
    BigRat worst_s(-1000);
    int worst_m = -1, worst_k = -1;
    for (long long denom = 1; denom <= 1000000000000000LL; denom *= 10) {
      AxisCertificate ax;
      BigVecQ3 ctr;
      BigRat del;
      std::string err;
      if (Tube229::AuditAxis(tri, c0, &ax, &ctr, &del, &err, BigRat(1, denom))) {
        // passes
      } else {
        std::cout << "Depth " << d << " passes defect <= 1/" << (denom / 10)
                  << " (" << (1.0 / (denom / 10)) << ")\n";
        break;
      }
    }
    path += "2";
  }
  return 0;
}
