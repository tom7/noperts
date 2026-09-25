#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int core_idx = 2951;
  const auto &core_ax = axes[core_idx];
  std::cout << "Core axis 2951 B: " << core_ax.cert.B.ToString() << " (" << core_ax.cert.B.ToDouble() << ")\n";
  std::cout << "Core axis 2951 delta: " << core_ax.delta.ToString() << " (" << core_ax.delta.ToDouble() << ")\n";
  std::cout << "Core axis 2951 center: (" << core_ax.center.x.ToDouble() << ", " << core_ax.center.y.ToDouble() << ", " << core_ax.center.z.ToDouble() << ")\n";
  double norm_center = std::sqrt(core_ax.center.x.ToDouble()*core_ax.center.x.ToDouble() +
                                 core_ax.center.y.ToDouble()*core_ax.center.y.ToDouble() +
                                 core_ax.center.z.ToDouble()*core_ax.center.z.ToDouble());
  std::cout << "Norm of center: " << norm_center << "\n";
  return 0;
}
