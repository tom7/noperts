#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo base[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };

  double best_delta = 1.0;
  int best_m[3] = {0, 0, 0};

  for (int m0 = 600; m0 <= 1000; m0 += 20) {
    for (int m1 = 600; m1 <= 1000; m1 += 20) {
      for (int m2 = 0; m2 <= 400; m2 += 20) {
        ContactInfo test[3] = {base[0], base[1], base[2]};
        test[0].mix = m0;
        test[1].mix = m1;
        test[2].mix = m2;

        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        std::string err;
        if (Tube229::AuditAxis(tri, test, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
          if (del.ToDouble() < best_delta) {
            best_delta = del.ToDouble();
            best_m[0] = m0; best_m[1] = m1; best_m[2] = m2;
            std::cout << "del0 new best: " << best_delta
                      << " with mixes (" << m0 << ", " << m1 << ", " << m2 << ")\n";
          }
        }
      }
    }
  }

  std::cout << "FINAL BEST DELTA FOR c0: " << best_delta
            << " with (" << best_m[0] << ", " << best_m[1] << ", " << best_m[2] << ")\n";
  return 0;
}
