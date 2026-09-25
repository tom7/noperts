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

  vec3 a = yocto::normalize(vec3{0.39639, -0.49234, -0.77493});

  std::vector<std::pair<double, int>> best_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= 0.000234013) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double d = yocto::dot(a, v);
      best_axes.push_back({d, (int)i});
    }
  }
  std::sort(best_axes.rbegin(), best_axes.rend());

  std::cout << "Top axes for this adversary:\n";
  for (int k = 0; k < 15; k++) {
    int idx = best_axes[k].second;
    std::cout << "  #" << k << ": idx " << idx << ": dot = " << best_axes[k].first
              << ", delta = " << axes[idx].delta.ToDouble() << "\n";
  }

  return 0;
}
