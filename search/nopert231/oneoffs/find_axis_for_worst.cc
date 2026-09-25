#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  vec3 worst_pt = vec3{0.401939, -0.481294, -0.778975};

  int best_idx = -1;
  double best_dot = -1e9;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000260) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      double d = yocto::dot(worst_pt, v);
      if (d > best_dot) {
        best_dot = d;
        best_idx = i;
      }
    }
  }

  std::cout << "Best axis for worst_pt: Axis " << best_idx
            << " with dot = " << best_dot
            << ", delta = " << axes[best_idx].delta.ToDouble()
            << ", norm = " << yocto::length(vec3{axes[best_idx].center.x.ToDouble() / axes[best_idx].cert.B.ToDouble(),
                                                axes[best_idx].center.y.ToDouble() / axes[best_idx].cert.B.ToDouble(),
                                                axes[best_idx].center.z.ToDouble() / axes[best_idx].cert.B.ToDouble()})
            << "\n";

  return 0;
}
