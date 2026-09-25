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

  vec3 c = {0.3992, -0.494824, -0.771874};
  c = yocto::normalize(c);

  // Complement cage axes: 0, 23, 24, 210
  for (int idx : {0, 23, 24, 210}) {
    double B = axes[idx].cert.B.ToDouble();
    vec3 v = vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B};
    double d = yocto::dot(c, v);
    std::cout << "Complement cage axis " << idx << ": dot = " << d
              << ", delta = " << axes[idx].delta.ToDouble() << "\n";
  }

  return 0;
}
