#include <iostream>
#include <iomanip>
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
  double norm_u0 = yocto::length(u0);
  vec3 u0_hat = u0 / norm_u0;

  vec3 k1 = vec3{1.0, 0.0, -u0.x / u0.z};
  k1 = k1 - yocto::dot(k1, u0_hat) * u0_hat;
  k1 = k1 / yocto::length(k1);
  vec3 k2 = yocto::cross(u0_hat, k1);

  double c_cone = 0.035;
  double c_core = 0.00055;
  double box_delta = 234013.0 / 1000000000.0;

  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  // Check box [9/16, 3/4] x [9/16, 3/4]
  double x_min = 9.0 / 16.0, x_max = 3.0 / 4.0;
  double y_min = 9.0 / 16.0, y_max = 3.0 / 4.0;
  int found = -1;
  double best_worst = -1e9;
  for (size_t a = 0; a < valid_axes.size(); a++) {
    vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
    double c1 = yocto::dot(v, k1);
    double c2 = yocto::dot(v, k2);
    double c0 = yocto::dot(v, u0_hat) / norm_u0;
    if (c0 >= 0) {
      double min_x = (c1 >= 0) ? c1 * x_min : c1 * x_max;
      double min_y = (c2 >= 0) ? c2 * y_min : c2 * y_max;
      double worst = min_x + min_y + c0 * c_cone;
      if (worst > best_worst) best_worst = worst;
      if (worst >= c_core) {
        found = a;
        break;
      }
    }
  }

  std::cout << "For [9/16, 3/4]^2: found=" << found << ", best_worst=" << best_worst << "\n";
  return 0;
}
