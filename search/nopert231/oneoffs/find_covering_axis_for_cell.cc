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

  // Depth 7 centroid: (0.3992, -0.494824, -0.771874)
  vec3 p = yocto::normalize(vec3{0.3992, -0.494824, -0.771874});

  std::cout << "Searching for axes covering point p = (" << p.x << ", " << p.y << ", " << p.z << "):\n";
  for (size_t i = 0; i < axes.size(); i++) {
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    double d = yocto::dot(p, v);
    double del = axes[i].delta.ToDouble();
    if (d > del) {
      std::cout << "  Axis " << i << ": dot = " << d << ", delta = " << del
                << ", margin = " << d - del << ", B = " << B << "\n";
    }
  }

  return 0;
}
