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

  double x1 = 18.7094, x2 = 18.7151;
  double y1 = -23.632, y2 = -23.6262;

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
  
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  auto check_pt = [&](double X, double Y, int a) {
    vec3 p = P0 + X * E1 + Y * E2;
    vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
    return yocto::dot(p, v) >= 0.00035 * yocto::length(p);
  };

  auto get_dot = [&](double X, double Y, int a) {
    vec3 p = P0 + X * E1 + Y * E2;
    vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                  axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
    return yocto::dot(yocto::normalize(p), v);
  };

  std::cout << "Testing 4 corners for cell:\n";
  int best_a = -1;
  double best_min_dot = -1.0;
  double box_delta = 234013.0 / 1000000000.0;
  for (size_t a = 0; a < axes.size(); a++) {
    if (axes[a].delta.ToDouble() > box_delta) continue;
    double d1 = get_dot(x1, y1, a);
    double d2 = get_dot(x2, y1, a);
    double d3 = get_dot(x2, y2, a);
    double d4 = get_dot(x1, y2, a);
    double min_d = std::min(std::min(d1, d2), std::min(d3, d4));
    if (min_d > best_min_dot) {
      best_min_dot = min_d;
      best_a = a;
    }
  }
  std::cout << "Best axis " << best_a << " with min_dot = " << best_min_dot << "\n";
  std::cout << "Dots: "
            << get_dot(x1, y1, best_a) << " "
            << get_dot(x2, y1, best_a) << " "
            << get_dot(x2, y2, best_a) << " "
            << get_dot(x1, y2, best_a) << "\n";
  std::cout << "Delta: " << axes[best_a].delta.ToDouble() << "\n";
  return 0;
}
