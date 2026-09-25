#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_ann[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c_ann, &cert0, &center0, &delta0, &err, BigRat(5, 1000));

  double B0 = cert0.B.ToDouble();
  double r = 1.0 / 2000.0;
  double r_min = 1.0 / 10000.0;
  double D0 = delta0.ToDouble();
  double delta = 3.33e-7;

  std::cout << "B0 = " << B0 << ", D0 = " << D0 << "\n";

  for (double c_cone : {0.015, 0.020, 0.030, 0.035, 0.040, 0.045}) {
    double lhs = std::pow(0.5 * r * r * B0 + D0, 2);
    double rhs = r_min * r_min * (1.0 - 0.25 * r * r) * std::pow((c_cone - delta) * B0, 2);
    std::cout << "c_cone = " << c_cone << ": lhs = " << lhs << ", rhs = " << rhs
              << " -> " << (lhs <= rhs ? "DOMINANCE PASS!" : "DOMINANCE FAIL")
              << " (margin ratio = " << rhs / lhs << ")\n";
  }

  return 0;
}
