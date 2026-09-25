#include <iostream>
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
  double D0 = 2.0e-7; // defect on the 3 vertices
  double delta = 3.33e-7;

  double c_cone = 0.040;
  double lhs = std::pow(0.5 * r * r * B0 + D0, 2);
  double rhs = r_min * r_min * (1.0 - 0.25 * r * r) * std::pow((c_cone - delta) * B0, 2);
  std::cout << "lhs = " << lhs << "\n";
  std::cout << "rhs = " << rhs << "\n";
  std::cout << "rhs / lhs = " << rhs / lhs << "\n";
  std::cout << (lhs <= rhs ? "PASS!" : "FAIL") << "\n";

  return 0;
}
