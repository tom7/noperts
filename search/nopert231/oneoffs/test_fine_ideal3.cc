#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  vec3 ideal3 = {0.865049, -0.461764, -0.196122};

  std::cout << "Testing GenerateCandidatesForView near ideal3 with cone_samples=20...\n";
  auto cands = Tube229::GenerateCandidatesForView(ideal3, tri, true, 20, true, 1e-4);
  std::cout << "Generated " << cands.size() << " candidates!\n";

  std::string err;
  int audited_count = 0;
  double max_dot = -1;
  for (const auto &cand : cands) {
    ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
      audited_count++;
      vec3 u = {center.x.ToDouble() / cert.B.ToDouble(),
                center.y.ToDouble() / cert.B.ToDouble(),
                center.z.ToDouble() / cert.B.ToDouble()};
      double d = yocto::dot(u / yocto::length(u), ideal3);
      if (d > max_dot) max_dot = d;
    }
  }
  std::cout << "Audited " << audited_count << " zero-defect axes! Max dot with ideal3: " << max_dot << "\n";
  return 0;
}
