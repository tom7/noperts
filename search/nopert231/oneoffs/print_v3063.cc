#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int idx = 3063;
  const auto &ax = axes[idx];
  double B = ax.cert.B.ToDouble();
  vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
  std::cout << "Axis 3063: v = (" << v.x << ", " << v.y << ", " << v.z << ")\n";
  std::cout << "delta = " << ax.delta.ToDouble() << "\n";
  return 0;
}
