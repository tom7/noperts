#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  std::cout << "Hull axis 0: delta = " << axes[0].delta.ToDouble() << "\n";
  std::cout << "Hull axis 24: delta = " << axes[24].delta.ToDouble() << "\n";
  std::cout << "Hull axis 210: delta = " << axes[210].delta.ToDouble() << "\n";

  return 0;
}
