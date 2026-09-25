#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  // Collect candidate contacts from ALL 24 vertices and all incident edges:
  std::vector<ContactInfo> all_contacts;
  std::vector<int> mixes = {0, 250, 500, 750, 1000};

  for (int v = 0; v < 24; v++) {
    // Find all incident edges to v
    std::vector<int> nbrs;
    for (int e = 0; e < 60; e++) {
      int a = Polyhedron::EdgeStart(e);
      int b = Polyhedron::EdgeFinish(e);
      if (a == v) nbrs.push_back(b);
      else if (b == v) nbrs.push_back(a);
    }
    // pairs of neighbors
    for (size_t i = 0; i < nbrs.size(); i++) {
      for (size_t j = i + 1; j < nbrs.size(); j++) {
        for (int mix : mixes) {
          ContactInfo ci;
          ci.vertex = v;
          ci.edge_start = nbrs[i];
          ci.edge_finish = v;
          ci.edge_start2 = v;
          ci.edge_finish2 = nbrs[j];
          ci.mix = mix;
          all_contacts.push_back(ci);
        }
      }
    }
  }

  std::cout << "Total candidate contacts: " << all_contacts.size() << "\n";
  return 0;
}
