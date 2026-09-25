#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  for (int idx : {1283, 4074, 1041}) {
    std::cout << "Axis " << idx << ": B = " << base_axes[idx].cert.B.ToString() << "\n";
    for (int m = 0; m < 3; m++) {
      const auto &c = base_axes[idx].cert.contacts[m];
      std::cout << "  contact " << m << ": vertex=" << c.vertex
                << ", edge=" << c.edge_start << "->" << c.edge_finish
                << ", edge2=" << c.edge_start2 << "->" << c.edge_finish2
                << ", mix=" << c.mix << "\n";
    }
  }
  return 0;
}
