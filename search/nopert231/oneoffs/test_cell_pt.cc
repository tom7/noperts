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

  vec3 p = {18.68, -23.86, -30.02};
  vec3 a = yocto::normalize(p);

  double best_dot = -1.0;
  int best_idx = -1;
  int count_35 = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(a, v);
    if (d > best_dot) {
      best_dot = d;
      best_idx = i;
    }
    if (d >= 0.00035) count_35++;
  }
  std::cout << "best_dot = " << best_dot << " (axis " << best_idx << ")\n";
  std::cout << "axes with dot >= 0.00035: " << count_35 << "\n";
  return 0;
}
