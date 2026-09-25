#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }
int main() {
  std::string target = "0312130021121220121212";
  TriangleQ tri = TriangleFromPath(target);
  TubeCertificate cert;
  std::string fail;
  // Let's run SynthesizeCertificateIterative and see the candidate pool and why it fails:
  vec3 tri_f[3] = {ToDouble(tri.corners[0]), ToDouble(tri.corners[1]), ToDouble(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> fine_mixes = {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000};
  std::vector<ContactInfo> contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  std::cout << "Generated " << contacts.size() << " contacts at centroid.\n";

  // Check how many 3-contact candidates pass DoubleCheckAxis:
  std::vector<Tube229::CandidateTriple> pool;
  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo triple[3] = {contacts[i], contacts[j], contacts[k]};
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri, triple, &cand)) {
          pool.push_back(cand);
        }
      }
    }
  }
  std::cout << "DoubleCheckAxis passed: " << pool.size() << " candidate axes.\n";

  // Check if any 4 can form a cage:
  std::array<int, 4> tet_indices;
  if (Tube229::FindExtremalTetrahedron(pool, &tet_indices)) {
    std::cout << "FindExtremalTetrahedron SUCCEEDED!\n";
  } else {
    std::cout << "FindExtremalTetrahedron FAILED (no enclosing tetrahedron).\n";
  }
  return 0;
}
