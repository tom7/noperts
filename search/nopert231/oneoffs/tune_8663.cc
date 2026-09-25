#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  int test_indices[2] = {8663, 9030};

  double box_delta = 165676.0 / 1000000000.0;

  for (int idx : test_indices) {
    const auto &ax = axes[idx];
    std::cout << "Testing axis " << idx << ", base delta = " << ax.delta.ToDouble() << "\n";
    ContactInfo base[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};

    double min_del = 1.0;
    int best_m[3] = {0, 0, 0};

    for (int m0 = 0; m0 <= 1000; m0 += 200) {
      for (int m1 = 0; m1 <= 1000; m1 += 200) {
        for (int m2 = 0; m2 <= 1000; m2 += 200) {
          ContactInfo test[3] = {base[0], base[1], base[2]};
          test[0].mix = m0; test[1].mix = m1; test[2].mix = m2;

          AxisCertificate cert;
          BigVecQ3 ctr;
          BigRat del;
          std::string err;
          if (Tube229::AuditAxis(tri, test, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
            double d = del.ToDouble();
            if (d < min_del) {
              min_del = d;
              best_m[0] = m0; best_m[1] = m1; best_m[2] = m2;
            }
          }
        }
      }
    }
    std::cout << "Axis " << idx << " best delta: " << min_del << " with mix ("
              << best_m[0] << ", " << best_m[1] << ", " << best_m[2] << ")\n";
    if (min_del <= box_delta) {
      std::cout << "SUCCESS! Axis " << idx << " satisfies delta <= box_delta!\n";
    }
  }

  return 0;
}
