#include <iostream>
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  vec3 sep_norm = {-0.401011, 0.483067, 0.778355};

  auto opposing = Tube229::FindOpposingCandidates(tri1, sep_norm, 50, 1e-12);
  std::cout << "FindOpposingCandidates returned " << opposing.size() << " candidates!\n";
  for (size_t i = 0; i < std::min((size_t)5, opposing.size()); i++) {
    double d = yocto::dot(opposing[i].normalized_a, sep_norm / yocto::length(sep_norm));
    std::cout << "  opposing[" << i << "]: dot=" << d << "\n";
    for (int m = 0; m < 3; m++) {
      const auto &c = opposing[i].contacts[m];
      std::cout << "    m=" << m << ": v=" << c.vertex
                << " edge=(" << c.edge_start << "->" << c.edge_finish
                << ", " << c.edge_start2 << "->" << c.edge_finish2
                << ") mix=" << c.mix << "\n";
    }
  }
  return 0;
}
