#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

int main() {
  std::string target = "0312130021121220121212";
  TriangleQ tri = TriangleFromPath(target);
  TubeCertificate cert;

  // Let's sample multiple directions around the sphere or from sibling:
  std::vector<ContactInfo> extra_contacts;
  // Sample sibling centroid:
  std::string sibling = "031213002112122012120";
  TriangleQ sib_tri = TriangleFromPath(sibling);
  vec3 sib_c = (ToDouble(sib_tri.corners[0]) + ToDouble(sib_tri.corners[1]) + ToDouble(sib_tri.corners[2])) / 3.0;
  auto sc = Tube229::GenerateSilhouetteContacts(sib_c, {0, 200, 400, 600, 800, 1000});
  extra_contacts.insert(extra_contacts.end(), sc.begin(), sc.end());

  if (Tube229::SynthesizeCertificateIterative(tri, 22, &cert, extra_contacts)) {
    std::cout << "SUCCESS! SynthesizeCertificateIterative certified child 2 with sibling contacts!\n";
  } else {
    std::cout << "Failed with sibling contacts.\n";
  }
  return 0;
}
