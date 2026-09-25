#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  for (int a : {47, 46, 58, 70, 57, 82, 34, 69}) {
    const auto &ax = axes[a];
    std::cout << "Axis " << a << ": B=" << ax.cert.B.ToString()
              << ", delta=" << ax.delta.ToString() << " (" << ax.delta.ToDouble() << ")\n";
    for (int i = 0; i < 3; i++) {
      const auto &c = ax.cert.contacts[i];
      std::cout << "  contact " << i << ": mix=" << c.mix
                << ", v=" << c.vertex
                << ", edge=" << c.edge_start << "->" << c.edge_finish
                << " & " << c.edge_start2 << "->" << c.edge_finish2 << "\n";
    }
  }
  return 0;
}
