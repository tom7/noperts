#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);
  BigVecQ3 center = (tri.corners[0] + tri.corners[1] + tri.corners[2]) / BigRat(3);
  vec3 view = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};

  std::vector<int> mixes = {0, 200, 400, 500, 600, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(view, mixes);
  std::cout << "Generated " << contacts.size() << " silhouette contacts.\n";
  for (size_t i = 0; i < contacts.size(); i += mixes.size()) {
    const auto& c = contacts[i];
    std::cout << "v=" << c.vertex << " (" << c.edge_start << "->" << c.edge_finish << ", "
              << c.edge_start2 << "->" << c.edge_finish2 << ")\n";
  }
  return 0;
}
