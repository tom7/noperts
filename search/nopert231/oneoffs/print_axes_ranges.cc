#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  double min_x = 1e9, max_x = -1e9;
  double min_y = 1e9, max_y = -1e9;
  double min_z = 1e9, max_z = -1e9;
  for (const auto &ax : base_axes) {
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    min_x = std::min(min_x, (double)u.x); max_x = std::max(max_x, (double)u.x);
    min_y = std::min(min_y, (double)u.y); max_y = std::max(max_y, (double)u.y);
    min_z = std::min(min_z, (double)u.z); max_z = std::max(max_z, (double)u.z);
  }
  std::cout << "x in [" << min_x << ", " << max_x << "]\n";
  std::cout << "y in [" << min_y << ", " << max_y << "]\n";
  std::cout << "z in [" << min_z << ", " << max_z << "]\n";
  return 0;
}
