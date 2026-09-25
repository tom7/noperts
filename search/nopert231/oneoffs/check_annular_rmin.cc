#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));

  double B0 = ann_cert.B.ToDouble();
  double r = 1.0 / 2000.0; // r_tube
  double c_cone = 0.015;
  double delta = ann_del.ToDouble();
  // For Axis 0, what is D0?
  // Let's compute support defect of Axis 0
  std::vector<ContactInfo> ann_v = {c_ann[0], c_ann[1], c_ann[2]};
  double D0 = Tube229::MaxSupportDefect(tri, ann_v, ann_cert).ToDouble();

  std::cout << "B0 = " << B0 << "\n";
  std::cout << "delta = " << delta << "\n";
  std::cout << "D0 = " << D0 << "\n";
  std::cout << "r = " << r << "\n";
  std::cout << "c_cone = " << c_cone << "\n";

  // r_min needed by annular dominance:
  // (0.5 * r^2 * B0 + D0) / ((c_cone - delta) * B0 * sqrt(1 - 0.25 * r^2))
  double num = 0.5 * r * r * B0 + D0;
  double den = (c_cone - delta) * B0 * std::sqrt(1.0 - 0.25 * r * r);
  double r_min = num / den;
  std::cout << "Required r_min >= " << r_min << "\n";

  // Now, what c_core is needed by line 769:
  // r_min^2 * (1 + (c_core - delta)^2) <= 4 * (c_core - delta)^2
  // (c_core - delta)^2 >= r_min^2 / (4 - r_min^2)
  // c_core >= delta + r_min / sqrt(4 - r_min^2)
  double min_c_core = delta + r_min / std::sqrt(4.0 - r_min * r_min);
  std::cout << "Required c_core >= " << min_c_core << "\n";

  return 0;
}
