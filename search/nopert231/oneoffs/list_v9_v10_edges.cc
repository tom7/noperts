#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  for (int v : {9, 10}) {
    std::cout << "Neighbors of vertex " << v << ":\n";
    for (int u = 0; u < 20; u++) {
      if (u == v) continue;
      BigVecQ3 diff = Tube229::VertexQ(u) - Tube229::VertexQ(v);
      double d = std::sqrt(diff.x.ToDouble()*diff.x.ToDouble() + diff.y.ToDouble()*diff.y.ToDouble() + diff.z.ToDouble()*diff.z.ToDouble());
      if (d < 0.6) {
        std::cout << "  u=" << u << " dist=" << d << "\n";
      }
    }
  }
  return 0;
}
