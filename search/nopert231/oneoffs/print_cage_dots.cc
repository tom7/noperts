#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  vec3 a = yocto::normalize(vec3{0.39639, -0.49234, -0.77493});
  for (int idx : {0, 24, 210}) {
    const auto &ax = axes[idx];
    double B = ax.cert.B.ToDouble();
    vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
    std::cout << "Cage axis " << idx << ": dot = " << yocto::dot(a, v) << ", delta = " << ax.delta.ToDouble() << "\n";
  }
  return 0;
}
