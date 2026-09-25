#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  vec3 n_seam = {0.237066, -0.757116, -0.182676};
  n_seam = yocto::normalize(n_seam);

  // Corner 2 view:
  vec3 u_c2 = {0.91602049, 0.20340275, 0.34573659};
  u_c2 = yocto::normalize(u_c2);

  std::cout << "Testing views across seam:\n";
  for (double step = -0.01; step <= 0.01; step += 0.002) {
    vec3 u = yocto::normalize(u_c2 + step * n_seam);
    double dot_seam = yocto::dot(u, n_seam);
    
    // Check caging with hull vertices:
    // Generate candidates:
    std::vector<ContactInfo> contacts;
    int hull_v[9] = {1, 2, 4, 8, 9, 10, 15, 19, 3};
    for (int v : hull_v) {
      for (const auto &c : Tube229::GenerateContactsForVertex(v)) {
        contacts.push_back(c);
      }
    }
    
    // Test if any 4-axis cage exists:
    // We can run FindBalancedTetrahedron
    std::vector<CandidateTriple> cands;
    for (const auto &c : contacts) {
      // test contacts
    }
    std::cout << "step=" << step << " dot_seam=" << dot_seam << "\n";
  }

  return 0;
}
