#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "FindAllHullSupportAxes returned " << axes.size() << " axes.\n";
  std::set<std::tuple<int, int, int>> distinct_v_triplets;
  for (const auto &ax : axes) {
    distinct_v_triplets.insert({ax.cert.contacts[0].vertex,
                                ax.cert.contacts[1].vertex,
                                ax.cert.contacts[2].vertex});
  }
  std::cout << "Distinct vertex triplets among generated axes: " << distinct_v_triplets.size() << "\n";
  for (const auto &trip : distinct_v_triplets) {
    std::cout << "  Triplet: (" << std::get<0>(trip) << ", " << std::get<1>(trip) << ", " << std::get<2>(trip) << ")\n";
  }
  return 0;
}
