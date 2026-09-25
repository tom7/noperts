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

  int flock_indices[5] = {3054, 119, 3063, 22, 24};
  for (int idx : flock_indices) {
    const auto &ax = axes[idx];
    double B = ax.cert.B.ToDouble();
    vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
    std::cout << "Axis " << idx << ": B = " << B << ", ||center|| = " << yocto::length(vec3{ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()})
              << ", ||v|| = " << yocto::length(v) << ", delta = " << ax.delta.ToDouble() << "\n";
  }
  return 0;
}
