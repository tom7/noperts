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

  // Sector 14 center from earlier:
  vec3 c = {0.3992, -0.494824, -0.771874};
  c = yocto::normalize(c);

  std::cout << "Searching across " << axes.size() << " axes for point c:\n";
  int found = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    double d = yocto::dot(c, v);
    double del = axes[i].delta.ToDouble();
    if (d > 0.005 && del <= 0.000235) {
      found++;
      std::cout << "  Axis " << i << ": dot = " << d << ", delta = " << del
                << ", B = " << B << ", margin = " << d - del << "\n";
    }
  }
  std::cout << "Total axes with dot > 0.005 and delta <= 0.000235: " << found << "\n";

  // Also search with no delta restriction:
  double max_d = -1.0; int best_i = -1;
  for (size_t i = 0; i < axes.size(); i++) {
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    double d = yocto::dot(c, v);
    if (d > max_d) { max_d = d; best_i = i; }
  }
  std::cout << "Absolute best axis: idx " << best_i << ", dot = " << max_d
            << ", delta = " << axes[best_i].delta.ToDouble() << "\n";
  return 0;
}
