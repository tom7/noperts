#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  const auto &ax = axes[3449];
  std::cout << "Original Axis 3449 delta = " << ax.delta.ToDouble() << "\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "Contact " << i << ": edge " << ax.cert.contacts[i].edge_start
              << " -> " << ax.cert.contacts[i].edge_finish
              << ", mix = " << ax.cert.contacts[i].mix
              << ", vertex = " << ax.cert.contacts[i].vertex << "\n";
  }

  ContactInfo info[3];
  for (int i = 0; i < 3; i++) info[i] = ax.cert.contacts[i];

  // Try tuning the mix parameters
  double best_delta = ax.delta.ToDouble();
  int best_m[3] = {info[0].mix, info[1].mix, info[2].mix};

  for (int m0 = 0; m0 <= 1000; m0 += 50) {
    for (int m1 = 0; m1 <= 1000; m1 += 50) {
      for (int m2 = 0; m2 <= 1000; m2 += 50) {
        ContactInfo test_info[3] = {info[0], info[1], info[2]};
        test_info[0].mix = m0;
        test_info[1].mix = m1;
        test_info[2].mix = m2;

        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        std::string err;
        if (Tube229::AuditAxis(tri, test_info, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
          if (del.ToDouble() < best_delta) {
            best_delta = del.ToDouble();
            best_m[0] = m0; best_m[1] = m1; best_m[2] = m2;
            std::cout << "New best delta: " << best_delta
                      << " with mixes (" << m0 << ", " << m1 << ", " << m2 << ")\n";
          }
        }
      }
    }
  }

  std::cout << "FINAL BEST DELTA for 3449: " << best_delta << "\n";
  return 0;
}
