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

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double u_sq = yocto::dot(u, u);

  // We want to test c_cone from 0.017 to 0.025
  // For each c_cone, and each axis, what is the maximum c_core achieved?
  for (double c_cone : {0.017, 0.020, 0.023, 0.025}) {
    double best_c_core = -1e9;
    int best_axis = -1;

    for (size_t i = 0; i < axes.size(); i++) {
      if (axes[i].delta.ToDouble() > 0.000280) continue;
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};

      double u_dot_v = yocto::dot(u, v);
      if (u_dot_v <= 0) continue;
      double lam = u_dot_v / u_sq;
      vec3 w = v - lam * u;
      double w_sq = yocto::dot(w, w);

      // hineq: w_sq * (u_sq - c_cone^2) <= u_sq * (lam * c_cone - c_core)^2
      // lam * c_cone - c_core >= sqrt(w_sq * (u_sq - c_cone^2) / u_sq)
      // c_core <= lam * c_cone - sqrt(w_sq * (u_sq - c_cone^2) / u_sq)
      if (u_sq < c_cone * c_cone) continue;
      double term = std::sqrt(w_sq * (u_sq - c_cone * c_cone) / u_sq);
      double max_c_core = lam * c_cone - term;
      if (max_c_core > best_c_core) {
        best_c_core = max_c_core;
        best_axis = i;
      }
    }
    std::cout << "c_cone = " << c_cone << ": best c_core = " << best_c_core
              << " (best axis " << best_axis << ", delta = "
              << (best_axis >= 0 ? axes[best_axis].delta.ToDouble() : 0) << ")\n";
  }
  return 0;
}
