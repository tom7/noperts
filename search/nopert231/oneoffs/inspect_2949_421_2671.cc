#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int indices[3] = {2949, 421, 2671};
  for (int idx : indices) {
    const auto &ax = base_axes[idx];
    std::cout << "Axis " << idx << ":\n";
    for (int i = 0; i < 3; i++) {
      std::cout << "  contact " << i << ": "
                << ax.cert.contacts[i].edge_start << "->" << ax.cert.contacts[i].edge_finish
                << " & " << ax.cert.contacts[i].edge_start2 << "->" << ax.cert.contacts[i].edge_finish2
                << " mix=" << ax.cert.contacts[i].mix << " v=" << ax.cert.contacts[i].vertex << "\n";
    }
    std::cout << "  u = ("
              << ax.center.x.ToDouble() / ax.cert.B.ToDouble() << ", "
              << ax.center.y.ToDouble() / ax.cert.B.ToDouble() << ", "
              << ax.center.z.ToDouble() / ax.cert.B.ToDouble() << ")\n";
    std::cout << "  B = " << ax.cert.B.ToDouble() << "\n";
  }
  return 0;
}
