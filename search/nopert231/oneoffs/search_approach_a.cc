#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double u0_len_sq = yocto::dot(u0, u0);

  double c_cone = 0.017;
  double box_delta = 165676.0 / 1000000000.0;

  std::cout << "Searching " << axes.size() << " axes for Approach A satisfaction...\n";

  int found = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    double del = ax.delta.ToDouble();
    if (del > box_delta) continue; // must be <= box.delta

    double B = ax.cert.B.ToDouble();
    vec3 u_core = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};

    double lam = yocto::dot(u_core, u0) / u0_len_sq;
    if (lam <= 0) continue;

    vec3 w = u_core - u0 * lam;
    double w_len_sq = yocto::dot(w, w);

    double c_core = box_delta; // minimum allowed c_core
    double margin = lam * c_cone - c_core;
    if (margin <= 0) continue;

    double lhs = w_len_sq * (u0_len_sq - c_cone * c_cone);
    double rhs = u0_len_sq * margin * margin;

    if (lhs <= rhs) {
      std::cout << "FOUND MATCH! Axis " << i << ":\n"
                << "  delta = " << del << "\n"
                << "  lam = " << lam << "\n"
                << "  w_len_sq = " << w_len_sq << "\n"
                << "  margin = " << margin << "\n"
                << "  lhs = " << lhs << ", rhs = " << rhs << "\n";
      found++;
    }
  }

  std::cout << "Total axes satisfying Approach A: " << found << "\n";
  return 0;
}
