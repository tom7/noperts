#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }

  for (double c_cone : {0.020, 0.022, 0.024, 0.026, 0.028, 0.030, 0.032, 0.035}) {
    double c1 = c_cone;
    double c2 = 0.000234060;
    double best_diff = -1e9;
    int best_a = -1;

    for (size_t a = 0; a < valid_axes.size(); a++) {
      vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                    valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                    valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
      double lam = yocto::dot(u0, v) / norm_u0_sq;
      if (lam < 0) continue;
      vec3 w = v - lam * u0;
      double norm_w_sq = yocto::dot(w, w);
      if (norm_w_sq < 1e-15) continue;
      double margin = lam * c1 - c2;
      if (margin <= 0) continue;

      double lhs = norm_w_sq * (norm_u0_sq - c1 * c1);
      double rhs = norm_u0_sq * (margin * margin);
      double diff = rhs - lhs;
      if (diff > best_diff) {
        best_diff = diff;
        best_a = a;
      }
    }
    std::cout << "c_cone = " << c_cone << ": best_diff = " << best_diff << " (axis " << best_a << ")\n";
  }
  return 0;
}
