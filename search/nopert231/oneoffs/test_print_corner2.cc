#include <iostream>
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  std::cout << "Corner 0: (" << tri1.corners[0].x.ToString() << ", " << tri1.corners[0].y.ToString() << ", " << tri1.corners[0].z.ToString() << ")\n";
  std::cout << "Corner 1: (" << tri1.corners[1].x.ToString() << ", " << tri1.corners[1].y.ToString() << ", " << tri1.corners[1].z.ToString() << ")\n";
  std::cout << "Corner 2: (" << tri1.corners[2].x.ToString() << ", " << tri1.corners[2].y.ToString() << ", " << tri1.corners[2].z.ToString() << ")\n";

  std::cout << "Corner 2 double: (" << tri1.corners[2].x.ToDouble() << ", " << tri1.corners[2].y.ToDouble() << ", " << tri1.corners[2].z.ToDouble() << ")\n";
  return 0;
}
