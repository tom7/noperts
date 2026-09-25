#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int count = 0;
  for (size_t i = 0; i < base_axes.size(); i++) {
    const auto &ax = base_axes[i];
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    if (u.z < -0.002 && u.y < 0) {
      count++;
      std::cout << "Axis " << i << ": u = (" << u.x << ", " << u.y << ", " << u.z << ")\n";
    }
  }
  std::cout << "Total axes with z < -0.002 and y < 0: " << count << "\n";
  return 0;
}
