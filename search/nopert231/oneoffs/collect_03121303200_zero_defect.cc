#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

struct Cand {
  ContactInfo c[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 u;
};

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  std::cout << "Searching for zero-defect axes for " << target_path << "...\n";

  std::vector<Cand> all_cands;
  std::string err;

  int N = 300;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto candidates = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    for (const auto &cand : candidates) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        vec3 u = {center.x.ToDouble() / cert.B.ToDouble(),
                  center.y.ToDouble() / cert.B.ToDouble(),
                  center.z.ToDouble() / cert.B.ToDouble()};
        all_cands.push_back({contacts[0], contacts[1], contacts[2], cert, center, delta, u});
      }
    }
  }

  std::cout << "Found " << all_cands.size() << " zero-defect axes!\n";
  return 0;
}
