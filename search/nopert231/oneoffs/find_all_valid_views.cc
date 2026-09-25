#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  int num_views = 0;
  int num_axes = 0;

  // Sample fibonacci sphere or spherical grid
  int N = 200;
  std::vector<Tube229::AuditedAxis> all_audited;

  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double phi = std::acos(z);
    double theta = M_PI * (1.0 + std::sqrt(5.0)) * i;
    vec3 v = {std::sin(phi) * std::cos(theta), std::sin(phi) * std::sin(theta), z};

    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 4, false);
    if (cands.empty()) continue;

    int valid_for_v = 0;
    std::string err;
    for (const auto &cand : cands) {
      ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
        all_audited.push_back({cert, center, delta});
        valid_for_v++;
      }
    }
    if (valid_for_v > 0) {
      num_views++;
      num_axes += valid_for_v;
      std::cout << "View " << i << " (" << v.x << ", " << v.y << ", " << v.z
                << ") gave " << valid_for_v << " axes (total " << num_axes << ")\n";
    }
  }

  std::cout << "Total views with valid axes: " << num_views << ", total axes: " << num_axes << "\n";
  return 0;
}
