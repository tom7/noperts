#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  const auto &a = axes[391];
  std::cout << "Axis 391:\n";
  std::cout << "  Center: (" << a.center.x.ToDouble() << ", " << a.center.y.ToDouble() << ", " << a.center.z.ToDouble() << ")\n";
  std::cout << "  Delta: " << a.delta.ToDouble() << "\n";
  std::cout << "  Contacts:\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "    [" << i << "] vertex " << a.cert.contacts[i].vertex
              << ", edge " << a.cert.contacts[i].edge_start << "->" << a.cert.contacts[i].edge_finish << "\n";
  }

  return 0;
}
