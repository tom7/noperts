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

  int chosen[] = {9030, 3449, 389, 36};
  for (int idx : chosen) {
    double B = axes[idx].cert.B.ToDouble();
    vec3 v = vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B};
    std::cout << "Axis " << idx << ": B = " << B << ", len = " << yocto::length(v)
              << ", delta = " << axes[idx].delta.ToDouble() << "\n";
  }
  return 0;
}
