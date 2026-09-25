#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  for (int idx : {22, 93, 94, 106}) {
    std::cout << "Axis " << idx << ": delta = " << axes[idx].delta.ToDouble()
              << ", B = " << axes[idx].cert.B.ToDouble() << "\n";
  }
  return 0;
}
