#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  // Let us compute the diameter/variation of tri
  BigVecQ3 v0 = tri.a, v1 = tri.b, v2 = tri.c;
  BigRat d01 = (v0 - v1).NormSquared();
  BigRat d12 = (v1 - v2).NormSquared();
  BigRat d20 = (v2 - v0).NormSquared();

  std::cout << "tri diameter squared: "
            << std::max({d01.ToDouble(), d12.ToDouble(), d20.ToDouble()}) << "\n";
  std::cout << "tri diameter: "
            << std::sqrt(std::max({d01.ToDouble(), d12.ToDouble(), d20.ToDouble()})) << "\n";
  return 0;
}
