#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  ContactInfo c0 = {3, 2, 2, 1, 800, 2};
  ContactInfo c1 = {1, 4, 4, 8, 800, 4};

  std::vector<ContactInfo> c2_opts = {
    {10, 15, 15, 19, 800, 15},
    {10, 15, 15, 19, 500, 15},
    {10, 15, 15, 19, 200, 15},
  };

  // Exceptional axis from Smoke.lean / sibling cert0:
  // u0 approx = normalize(cand0.normalized_a)
  vec3 uncov = normalize(vec3{0.400992, -0.483041, -0.778381});
  vec3 neg_uncov = uncov * -1.0;

  for (size_t idx = 0; idx < c2_opts.size(); idx++) {
    ContactInfo c[3] = {c0, c1, c2_opts[idx]};
    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri1, c, &cand, 0.0);
    std::cout << "Opt " << idx << " (mix=" << c2_opts[idx].mix << "): " << (ok ? "PASS" : "FAIL") << "\n";
    if (ok) {
      std::cout << "  norm_a = (" << cand.normalized_a.x << ", "
                << cand.normalized_a.y << ", " << cand.normalized_a.z << ")\n";
      std::cout << "  dot(norm_a, uncov) = " << yocto::dot(cand.normalized_a, uncov) << "\n";
      std::cout << "  dot(norm_a, neg_uncov) = " << yocto::dot(cand.normalized_a, neg_uncov) << "\n";
    }
  }

  return 0;
}
