#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // Look at axis 4907 or axis 74 or axis 391
  for (int idx : {74, 391, 3058, 4907}) {
    std::cout << "Axis " << idx << ":\n";
    std::cout << "  del = " << axes[idx].delta.ToDouble() << "\n";
    std::cout << "  B = " << axes[idx].cert.B.ToDouble() << "\n";
  }
  return 0;
}
