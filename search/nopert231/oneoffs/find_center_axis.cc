#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  vec3 a_dir = {0.00703944, 0.0540474, -0.998514};
  double box_delta = 234013.0 / 1000000000.0;

  double best_dot = -1e9;
  int best_idx = -1;

  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= box_delta) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = {axes[i].center.x.ToDouble() / B,
                axes[i].center.y.ToDouble() / B,
                axes[i].center.z.ToDouble() / B};
      double d = yocto::dot(a_dir, v);
      if (d > best_dot) {
        best_dot = d;
        best_idx = i;
      }
    }
  }

  std::cout << "Best axis among 5000 with delta <= box_delta:\n"
            << "Index " << best_idx << ", dot = " << best_dot
            << ", delta = " << axes[best_idx].delta.ToDouble() << "\n";
  std::cout << "Contacts:\n";
  for (int k = 0; k < 3; k++) {
    const auto &c = axes[best_idx].cert.contacts[k];
    std::cout << "  (" << c.edge_start << "->" << c.edge_finish << " & "
              << c.edge_start2 << "->" << c.edge_finish2 << "), mix="
              << c.mix << ", v=" << c.vertex << "\n";
  }

  return 0;
}
