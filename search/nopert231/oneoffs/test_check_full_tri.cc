#include <iostream>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  ContactInfo c0 = {3, 2, 2, 1, 800, 2};
  ContactInfo c1 = {1, 4, 4, 8, 800, 4};

  std::vector<ContactInfo> c2_opts = {
    {15, 19, 15, 19, 1000, 15},
    {14, 15, 15, 19, 800, 15},
    {14, 15, 15, 19, 500, 15},
    {14, 15, 15, 19, 200, 15},
    {14, 15, 15, 19, 0, 15},
    {10, 15, 15, 19, 800, 15},
    {10, 15, 15, 19, 500, 15},
    {10, 15, 15, 19, 200, 15},
    {10, 15, 15, 19, 0, 15},
    {19, 3, 19, 3, 1000, 19},
    {15, 19, 19, 3, 500, 19},
  };

  for (size_t idx = 0; idx < c2_opts.size(); idx++) {
    ContactInfo c[3] = {c0, c1, c2_opts[idx]};
    Tube229::CandidateTriple cand;
    bool ok = Tube229::DoubleCheckAxis(tri1, c, &cand, 0.0);
    std::cout << "Opt " << idx << ": " << (ok ? "PASS" : "FAIL");
    if (ok) {
      std::cout << " | slack = " << cand.strict_slack << ", B = " << cand.B
                << ", norm_a = (" << cand.normalized_a.x << ", "
                << cand.normalized_a.y << ", " << cand.normalized_a.z << ")";
    }
    std::cout << "\n";
  }
  return 0;
}
