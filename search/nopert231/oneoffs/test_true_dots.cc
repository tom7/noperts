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

  vec3 a_cart = yocto::normalize(vec3{0.39807, -0.48083, -0.78137});

  double max_dot = -1.0;
  int best_ax = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= 0.000234013) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double d = yocto::dot(a_cart, v);
      if (d > max_dot) {
        max_dot = d;
        best_ax = i;
      }
    }
  }

  std::cout << "True best dot with candidate axes: " << max_dot << " (axis " << best_ax << ", delta = "
            << axes[best_ax].delta.ToDouble() << ")\n";
  return 0;
}
