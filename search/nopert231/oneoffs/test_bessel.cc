#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

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
    if (ax.delta.ToDouble() <= box_delta) {
      valid_axes.push_back(ax);
    }
  }

  // Also add grid axes
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
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({cert, ctr, del});
        }
      }
    }
  }

  std::cout << "Testing " << valid_axes.size() << " valid axes for Bessel coverage:\n";
  for (double c_cone : {0.015, 0.020, 0.025, 0.028, 0.035}) {
    for (double c_core : {0.0001, 0.0002, 0.0003, 0.001, 0.005, 0.010}) {
      double c1 = c_cone;
      double c2 = c_core;
      if (norm_u0_sq <= c1 * c1) continue;

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
        if (lhs <= rhs) {
          std::cout << "SUCCESS! c_cone = " << c_cone << ", c_core = " << c_core
                    << " covered by axis " << a << " (margin diff = " << rhs - lhs << ")\n";
        }
      }
    }
  }
  return 0;
}
