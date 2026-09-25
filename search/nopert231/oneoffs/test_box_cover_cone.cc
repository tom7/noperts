#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>
#include <algorithm>
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

  // Choose orthonormal frame k1, k2 in u0_hat^perp
  vec3 k1 = vec3{1.0, 0.0, -u0.x / u0.z};
  k1 = k1 - yocto::dot(k1, u0_hat) * u0_hat;
  k1 = k1 / yocto::length(k1);
  vec3 k2 = yocto::cross(u0_hat, k1);

  double c_cone = 0.035;
  double c_core = 0.00055;
  double box_delta = 234013.0 / 1000000000.0;

  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) {
      valid_axes.push_back(ax);
    }
  }

  // Also add grid of contact mixes
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

  struct Decomp {
    int axis_id;
    double c1, c2, c0;
  };
  std::vector<Decomp> decomps;
  for (size_t a = 0; a < valid_axes.size(); a++) {
    vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
    double c1 = yocto::dot(v, k1);
    double c2 = yocto::dot(v, k2);
    // We want dot(v, a) = c1 * (a . k1) + c2 * (a . k2) + c0 * (a . u0)
    // In our orthonormal basis:
    // a = x * k1 + y * k2 + z * u0_hat
    // so dot(v, a) = dot(v, k1)*x + dot(v, k2)*y + dot(v, u0_hat)*z
    // And (a . u0) = z * norm_u0 >= c_cone  ==> z >= c_cone / norm_u0.
    // If dot(v, u0_hat) >= 0:
    // dot(v, u0_hat) * z >= dot(v, u0_hat) * (c_cone / norm_u0) = c0 * c_cone,
    // where c0 = dot(v, u0_hat) / norm_u0.
    double c0 = yocto::dot(v, u0_hat) / norm_u0;
    if (c0 >= 0) {
      decomps.push_back({(int)a, c1, c2, c0});
    }
  }

  std::cout << "Valid axes with c0 >= 0: " << decomps.size() << "\n";

  auto check_box = [&](double x_min, double x_max, double y_min, double y_max) {
    for (const auto &d : decomps) {
      double min_x = (d.c1 >= 0) ? d.c1 * x_min : d.c1 * x_max;
      double min_y = (d.c2 >= 0) ? d.c2 * y_min : d.c2 * y_max;
      double worst = min_x + min_y + d.c0 * c_cone;
      if (worst >= c_core) {
        return d.axis_id;
      }
    }
    return -1;
  };

  double max_sin = std::sqrt(1.0 - (c_cone / norm_u0) * (c_cone / norm_u0));
  std::cout << "max_sin = " << max_sin << "\n";

  int leaves = 0;
  auto subdivide = [&](auto& self, double x1, double x2, double y1, double y2, int depth) -> bool {
    // If box is outside circle of radius max_sin:
    double min_x = (x1 <= 0 && 0 <= x2) ? 0 : std::min(std::abs(x1), std::abs(x2));
    double min_y = (y1 <= 0 && 0 <= y2) ? 0 : std::min(std::abs(y1), std::abs(y2));
    if (min_x * min_x + min_y * min_y > max_sin * max_sin) {
      return true; // outside cone!
    }

    int ax = check_box(x1, x2, y1, y2);
    if (ax >= 0) {
      leaves++;
      std::cout << "Leaf " << leaves << ": [" << x1 << ", " << x2 << "] x ["
                << y1 << ", " << y2 << "], axis " << ax << "\n";
      return true;
    }
    if (depth >= 12) return false;
    double xm = 0.5 * (x1 + x2);
    double ym = 0.5 * (y1 + y2);
    return self(self, x1, xm, y1, ym, depth + 1) &&
           self(self, xm, x2, y1, ym, depth + 1) &&
           self(self, x1, xm, ym, y2, depth + 1) &&
           self(self, xm, x2, ym, y2, depth + 1);
  };

  double S = 11.0 / 16.0;
  bool ok = subdivide(subdivide, -S, S, -S, S, 0);
  std::cout << "Box cover of cone with S=11/16: ok=" << ok << ", leaves=" << leaves << "\n";

  return 0;
}
