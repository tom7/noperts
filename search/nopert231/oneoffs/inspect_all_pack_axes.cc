#include <iostream>
#include <set>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::vector<char> packed = CC_ReadEntireFile("local-view0.pack");
  std::cout << "Read " << packed.size() << " bytes.\n";

  // Let's count how many leaves exist and what their axes are:
  // tubetree229 has deserializer:
  TubeTree tree = TubeTree::Deserialize(packed);
  std::cout << "Tree leaves: " << tree.NumLeaves() << "\n";

  std::set<std::tuple<int, int, int>> distinct_triples;
  std::vector<TubeCertificate> all_certs;
  tree.CollectCertificates(&all_certs);
  std::cout << "Total certificates: " << all_certs.size() << "\n";

  return 0;
}
