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
  double norm_u0 = yocto::length(u0);
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  // The problematic adversary point in Cartesian was:
  vec3 a_cart = yocto::normalize(vec3{0.39807, -0.48083, -0.78137});
  double x = yocto::dot(a_cart, k1);
  double y = yocto::dot(a_cart, k2);
  double z = yocto::dot(a_cart, e3);

  std::cout << "In basis (k1, k2, e3): x = " << x << ", y = " << y << ", z = " << z << "\n";
  std::cout << "x^2 + y^2 + z^2 = " << x*x + y*y + z*z << "\n";

  // Let's create a small 2D box around (x, y) of size 0.005
  double eps = 0.002;
  double x_min = x - eps, x_max = x + eps;
  double y_min = y - eps, y_max = y + eps;

  double min_x = (x_min <= 0 && x_max >= 0) ? 0.0 : std::min(std::abs(x_min), std::abs(x_max));
  double min_y = (y_min <= 0 && y_max >= 0) ? 0.0 : std::min(std::abs(y_min), std::abs(y_max));
  double r_min_sq = min_x * min_x + min_y * min_y;

  double max_x = std::max(std::abs(x_min), std::abs(x_max));
  double max_y = std::max(std::abs(y_min), std::abs(y_max));
  double r_max_sq = max_x * max_x + max_y * max_y;

  double z_min = std::sqrt(std::max(0.0, 1.0 - r_max_sq));
  double z_max = std::sqrt(std::max(0.0, 1.0 - r_min_sq));

  std::cout << "r_min_sq = " << r_min_sq << ", r_max_sq = " << r_max_sq << "\n";
  std::cout << "z_min = " << z_min << ", z_max = " << z_max << "\n";

  double best_val = -1e9;
  int best_ax = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= 0.000234013) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double c1 = yocto::dot(v, k1);
      double c2 = yocto::dot(v, k2);
      double cz = yocto::dot(v, e3);

      double c1_c = (c1 >= 0 ? c1 * x_min : c1 * x_max);
      double c2_c = (c2 >= 0 ? c2 * y_min : c2 * y_max);
      double cz_c = (cz >= 0 ? cz * z_min : cz * z_max);
      double val = c1_c + c2_c + cz_c;
      if (val > best_val) {
        best_val = val;
        best_ax = i;
      }
    }
  }

  std::cout << "Best axis " << best_ax << ": val = " << best_val
            << ", delta = " << axes[best_ax].delta.ToDouble() << "\n";

  return 0;
}

// Let's print the actual dot products of a with all axes
