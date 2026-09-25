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
  std::cout << "Loaded " << base_axes.size() << " axes.\n";
  int count_lt_1e4 = 0, count_lt_5e4 = 0, count_lt_1e3 = 0;
  double min_d = 1e9, max_d = 0;
  for (const auto &ax : base_axes) {
    double d = ax.delta.ToDouble();
    min_d = std::min(min_d, d);
    max_d = std::max(max_d, d);
    if (d < 1e-4) count_lt_1e4++;
    if (d < 5e-4) count_lt_5e4++;
    if (d < 1e-3) count_lt_1e3++;
  }
  std::cout << "min_d = " << min_d << ", max_d = " << max_d << "\n";
  std::cout << "count < 1e-4: " << count_lt_1e4 << "\n";
  std::cout << "count < 5e-4: " << count_lt_5e4 << "\n";
  std::cout << "count < 1e-3: " << count_lt_1e3 << "\n";
  return 0;
}
