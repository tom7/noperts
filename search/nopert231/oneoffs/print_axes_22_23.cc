#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Axis 22:\n";
  std::cout << "delta: " << axes[22].delta.ToDouble() << "\n";
  std::cout << "contacts:\n";
  for (int i = 0; i < 3; i++) {
    const auto &c = axes[22].cert.contacts[i];
    std::cout << "  v=" << c.vertex << " mix=" << c.mix
              << " (" << c.edge_start << "->" << c.edge_finish
              << " & " << c.edge_start2 << "->" << c.edge_finish2 << ")\n";
  }
  std::cout << "Axis 23:\n";
  std::cout << "delta: " << axes[23].delta.ToDouble() << "\n";
  std::cout << "contacts:\n";
  for (int i = 0; i < 3; i++) {
    const auto &c = axes[23].cert.contacts[i];
    std::cout << "  v=" << c.vertex << " mix=" << c.mix
              << " (" << c.edge_start << "->" << c.edge_finish
              << " & " << c.edge_start2 << "->" << c.edge_finish2 << ")\n";
  }
  return 0;
}
