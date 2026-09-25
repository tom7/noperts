#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  double min_x = 1e9, max_x = -1e9;
  double min_y = 1e9, max_y = -1e9;
  double min_z = 1e9, max_z = -1e9;
  double max_norm = 0;

  for (size_t i = 0; i < base_axes.size(); i++) {
    double x = base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble();
    double y = base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble();
    double z = base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble();
    min_x = std::min(min_x, x); max_x = std::max(max_x, x);
    min_y = std::min(min_y, y); max_y = std::max(max_y, y);
    min_z = std::min(min_z, z); max_z = std::max(max_z, z);
    double norm = sqrt(x*x + y*y + z*z);
    max_norm = std::max(max_norm, norm);
  }

  std::cout << "x range: [" << min_x << ", " << max_x << "]\n";
  std::cout << "y range: [" << min_y << ", " << max_y << "]\n";
  std::cout << "z range: [" << min_z << ", " << max_z << "]\n";
  std::cout << "max_norm: " << max_norm << "\n";

  return 0;
}
