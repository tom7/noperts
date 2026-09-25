#include <iostream>
#include <string>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

int main() {
  std::string parent = "03121303200";
  for (int c = 0; c < 4; c++) {
    std::string child = parent + std::to_string(c);
    TriangleQ tri = TriangleFromPath(child);
    std::cout << "\nChild: " << child << "\n";

    // Try finding standard 4-axis zero-defect cage:
    auto axes = Tube229::FindAllHullSupportAxes(tri, 200);
    std::cout << "  Zero-defect axes: " << axes.size() << "\n";

    // Check if any zero defect axes cage origin:
    int N = axes.size();
    bool found_cage = false;
    for (int i0 = 0; i0 < N && !found_cage; i0++) {
      vec3 c0 = {axes[i0].center.x.ToDouble(), axes[i0].center.y.ToDouble(), axes[i0].center.z.ToDouble()};
      for (int i1 = i0 + 1; i1 < N && !found_cage; i1++) {
        vec3 c1 = {axes[i1].center.x.ToDouble(), axes[i1].center.y.ToDouble(), axes[i1].center.z.ToDouble()};
        for (int i2 = i1 + 1; i2 < N && !found_cage; i2++) {
          vec3 c2 = {axes[i2].center.x.ToDouble(), axes[i2].center.y.ToDouble(), axes[i2].center.z.ToDouble()};
          for (int i3 = i2 + 1; i3 < N && !found_cage; i3++) {
            vec3 c3 = {axes[i3].center.x.ToDouble(), axes[i3].center.y.ToDouble(), axes[i3].center.z.ToDouble()};

            double V0 = yocto::dot(c1, yocto::cross(c2, c3));
            double V1 = -yocto::dot(c0, yocto::cross(c2, c3));
            double V2 = yocto::dot(c0, yocto::cross(c1, c3));
            double V3 = -yocto::dot(c0, yocto::cross(c1, c2));

            double total = V0 + V1 + V2 + V3;
            if (std::abs(total) < 1e-9) continue;

            if (V0 / total > 1e-4 && V1 / total > 1e-4 && V2 / total > 1e-4 && V3 / total > 1e-4) {
              std::cout << "  FOUND PURE ZERO-DEFECT CAGE!\n";
              found_cage = true;
            }
          }
        }
      }
    }
    if (!found_cage) {
      std::cout << "  No pure zero-defect cage.\n";
    }
  }
  return 0;
}
