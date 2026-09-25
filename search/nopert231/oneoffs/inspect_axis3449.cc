#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  int idx = 3449;
  const auto &ax = axes[idx];
  std::cout << "Axis 3449:\n";
  std::cout << "  B = " << ax.cert.B.ToString() << "\n";
  std::cout << "  delta = " << ax.delta.ToDouble() << "\n";
  std::cout << "  center = (" << ax.center.x.ToString() << ", "
                              << ax.center.y.ToString() << ", "
                              << ax.center.z.ToString() << ")\n";

  return 0;
}
