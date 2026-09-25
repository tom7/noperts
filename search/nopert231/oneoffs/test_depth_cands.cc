#include <iostream>
#include <vector>
#include <string>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string full = "031213002112122012121";
  for (size_t len = 8; len <= full.size(); len++) {
    std::string path = full.substr(0, len);
    TriangleQ tri = TriangleFromPath(path);
    auto c0 = tri.corners[0];
    auto c1 = tri.corners[1];
    auto c2 = tri.corners[2];
    vec3 v0 = vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};
    vec3 v1 = vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()};
    vec3 v2 = vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()};
    vec3 centroid = (v0 + v1 + v2) / 3.0;

    auto cands = Tube229::GenerateCandidatesForView(centroid, tri, false, 0, false, 1e-12);
    std::cout << "Depth " << len << " (" << path << "): candidates = " << cands.size() << "\n";
    if (cands.size() > 0) {
      int zero_count = 0;
      std::string err;
      for (const auto &c : cands) {
        AxisCertificate cert;
        BigVecQ3 center;
        BigRat delta;
        ContactInfo contacts[3] = {c.contacts[0], c.contacts[1], c.contacts[2]};
        if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
          zero_count++;
        }
      }
      std::cout << "   Audited zero-defect axes = " << zero_count << "\n";
      if (zero_count > 100) break;
    }
  }
  return 0;
}
