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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = {ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  double B = ann_cert.B.ToDouble();
  double delta = 0.000234013;
  double D0 = 0.000118; // conservative upper bound

  auto det4 = [](const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d) {
    auto d3 = [](const vec3 &x, const vec3 &y, const vec3 &z) {
      return yocto::dot(x, yocto::cross(y, z));
    };
    return -d3(b, c, d) + d3(a, c, d) - d3(a, b, d) + d3(a, b, c);
  };

  std::vector<vec3> p(axes.size());
  for (size_t i = 0; i < axes.size(); i++) {
    p[i] = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
            axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
            axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
  }

  // We sweep c_cone from 0.008 to 0.020:
  for (double c_cone = 0.008; c_cone <= 0.022; c_cone += 0.001) {
    // Under this c_cone, find min r required by annular dominance:
    // With r_min = 0.98 * r:
    // (0.5 * r^2 * B + D0) <= r_min * sqrt(1 - 0.25 * r^2) * (c_cone - delta) * B
    // Let's find if any r in [0.001, 0.020] satisfies this:
    double r_needed = -1;
    for (double r_test = 0.001; r_test <= 0.020; r_test += 0.0001) {
      double r_min = 0.98 * r_test;
      double lhs = 0.5 * r_test * r_test * B + D0;
      double rhs = r_min * std::sqrt(std::max(0.0, 1.0 - 0.25 * r_test * r_test)) * (c_cone - delta) * B;
      if (lhs <= rhs) {
        r_needed = r_test;
        break;
      }
    }
    if (r_needed < 0) continue;

    // To satisfy comp_angle, we need r^2 (1 + (c-delta)^2) <= 4 (c-delta)^2
    // Approximately: c - delta >= r / 2  =>  c >= r/2 + delta
    double c_needed = 0.5 * r_needed / std::sqrt(1.0 - 0.25 * r_needed * r_needed) + delta + 1e-5;

    std::cout << "c_cone = " << c_cone << " => requires r >= " << r_needed
              << ", requires c >= " << c_needed << "\n";

    // Can we achieve this c_needed?
    bool found = false;
    for (size_t i = 0; i < axes.size() && !found; i++) {
      for (size_t j = i + 1; j < axes.size() && !found; j++) {
        for (size_t k = j + 1; k < axes.size() && !found; k++) {
          double s = (c_needed + delta) / c_cone;
          vec3 p0 = s * u0;
          double R = 1.75 * (c_needed + delta);
          vec3 oct[6] = {
            {R, 0, 0}, {-R, 0, 0},
            {0, R, 0}, {0, -R, 0},
            {0, 0, R}, {0, 0, -R}
          };
          double D = det4(p0, p[i], p[j], p[k]);
          if (D <= 1e-9) continue;
          bool ok = true;
          for (int m = 0; m < 6; m++) {
            double l0 = det4(oct[m], p[i], p[j], p[k]) / D;
            double l1 = det4(p0, oct[m], p[j], p[k]) / D;
            double l2 = det4(p0, p[i], oct[m], p[k]) / D;
            double l3 = det4(p0, p[i], p[j], oct[m]) / D;
            if (l0 <= 1e-6 || l1 <= 1e-6 || l2 <= 1e-6 || l3 <= 1e-6) {
              ok = false; break;
            }
          }
          if (ok) {
            std::cout << "  FOUND FEASIBLE TRIPLE (" << i << ", " << j << ", " << k
                      << ") at c_cone=" << c_cone << ", c=" << c_needed << ", r=" << r_needed << "!\n";
            found = true;
          }
        }
      }
    }
  }
  return 0;
}
