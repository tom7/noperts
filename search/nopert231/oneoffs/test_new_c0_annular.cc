#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 100, 2},
    {1, 4, 4, 8, 0, 4},
    {13, 14, 14, 15, 1000, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = std::sqrt(yocto::dot(u0, u0));
  std::cout << "norm_u0 = " << norm_u0 << "\n";

  double r = 4.0 / 100000.0;
  double r_min = 0.0003;
  double c_cone = 0.017;
  double box_delta = 160.0 / 1000000.0;

  double D0 = 0.0; // Is defect 0?
  // Check annular dominance:
  // ((1/2) * r^2 * B0 + D0)^2 <= r_min^2 * (1 - (1/4)*r^2) * ((c_cone - box_delta)^2 * B0^2)
  double lhs = 0.5 * r * r * B0 + D0;
  lhs = lhs * lhs;
  double rhs = r_min * r_min * (1.0 - 0.25 * r * r) * ((c_cone - box_delta) * (c_cone - box_delta) * B0 * B0);

  std::cout << "Annular dominance LHS = " << lhs << ", RHS = " << rhs << ", ratio = " << (lhs / rhs) << "\n";
  if (lhs <= rhs) {
    std::cout << "ANNULAR DOMINANCE HOLDS WITH HUGE MARGIN!\n";
  }

  // Core angle condition:
  // r_min^2 * (1 + (c_core - box_delta)^2) <= 4 * (c_core - box_delta)^2
  double c_core = 0.000161;
  double margin = c_core - box_delta; // 1e-6
  double core_lhs = r_min * r_min * (1.0 + margin * margin);
  double core_rhs = 4.0 * margin * margin;
  std::cout << "Core angle LHS = " << core_lhs << ", RHS = " << core_rhs << "\n";
  // If margin is 1e-6, r_min needs to be <= 2 * 1e-6 = 2e-6.
  // Can r_min be smaller?
  // What is the smallest r_min that satisfies annular dominance?
  double min_rmin = std::sqrt(lhs / ((1.0 - 0.25 * r * r) * ((c_cone - box_delta) * (c_cone - box_delta) * B0 * B0)));
  std::cout << "Minimum required r_min for annular dominance = " << min_rmin << "\n";

  return 0;
}
