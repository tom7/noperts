#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int chosen[] = {3054, 119, 3063, 22, 24};
  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del; std::string err;
    bool ok = Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(1, 1000));
    std::cout << "Axis " << idx << " (contacts: " << cts[0].vertex << ", " << cts[1].vertex << ", " << cts[2].vertex << "): ";
    if (ok) {
      std::cout << "B = " << cert.B.ToDouble() << ", delta = " << del.ToDouble() << "\n";
    } else {
      std::cout << "AUDIT FAILED: " << err << "\n";
    }
  }
  return 0;
}
