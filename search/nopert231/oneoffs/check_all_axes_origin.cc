#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // Check min and max coordinates of audited zero-defect axes:
  double min_x = 1e9, max_x = -1e9;
  double min_y = 1e9, max_y = -1e9;
  double min_z = 1e9, max_z = -1e9;

  int zd_count = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    // Only pure zero defect:
    if (axes[i].del != BigRat(0)) continue;
    zd_count++;
    double x = axes[i].center.x.ToDouble();
    double y = axes[i].center.y.ToDouble();
    double z = axes[i].center.z.ToDouble();
    if (x < min_x) min_x = x;
    if (x > max_x) max_x = x;
    if (y < min_y) min_y = y;
    if (y > max_y) max_y = y;
    if (z < min_z) min_z = z;
    if (z > max_z) max_z = z;
  }

  std::cout << "Pure zero-defect axes count: " << zd_count << "\n";
  std::cout << "x range: [" << min_x << ", " << max_x << "]\n";
  std::cout << "y range: [" << min_y << ", " << max_y << "]\n";
  std::cout << "z range: [" << min_z << ", " << max_z << "]\n";

  return 0;
}
