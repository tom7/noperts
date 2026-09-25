#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  // Axes 1, 2, 3 from sibling n0:
  ContactInfo ax1[3] = { {15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9} };
  ContactInfo ax2[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15} };
  ContactInfo ax3[3] = { {3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15} };

  ContactInfo c0 = {3, 2, 2, 1, 800, 2};
  ContactInfo c1 = {1, 4, 4, 8, 800, 4};

  std::vector<ContactInfo> c2_candidates = {
    {10, 15, 15, 19, 800, 15},
    {10, 15, 15, 19, 700, 15},
    {10, 15, 15, 19, 600, 15},
    {10, 15, 15, 19, 500, 15},
    {10, 15, 15, 19, 400, 15},
    {10, 15, 15, 19, 300, 15},
    {10, 15, 15, 19, 200, 15},
  };

  Tube229::CandidateTriple cand[4];
  bool ok1 = Tube229::DoubleCheckAxis(tri1, ax1, &cand[1], 0.0);
  bool ok2 = Tube229::DoubleCheckAxis(tri1, ax2, &cand[2], 0.0);
  bool ok3 = Tube229::DoubleCheckAxis(tri1, ax3, &cand[3], 0.0);

  std::cout << "Axes 1, 2, 3 check: "
            << "ax1=" << (ok1 ? "OK" : "FAIL") << ", "
            << "ax2=" << (ok2 ? "OK" : "FAIL") << ", "
            << "ax3=" << (ok3 ? "OK" : "FAIL") << "\n";

  for (size_t i = 0; i < c2_candidates.size(); i++) {
    ContactInfo ax0[3] = {c0, c1, c2_candidates[i]};
    bool ok0 = Tube229::DoubleCheckAxis(tri1, ax0, &cand[0], 0.0);
    if (!ok0) continue;

    // Check barycentric coverage of 0
    vec3 p0 = cand[0].normalized_a;
    vec3 p1 = cand[1].normalized_a;
    vec3 p2 = cand[2].normalized_a;
    vec3 p3 = cand[3].normalized_a;

    vec3 a = p0 - p3;
    vec3 b = p1 - p3;
    vec3 c = p2 - p3;
    double det = yocto::dot(a, yocto::cross(b, c));
    vec3 rhs = -p3;
    double w0 = yocto::dot(rhs, yocto::cross(b, c)) / det;
    double w1 = yocto::dot(a, yocto::cross(rhs, c)) / det;
    double w2 = yocto::dot(a, yocto::cross(b, rhs)) / det;
    double w3 = 1.0 - w0 - w1 - w2;

    std::cout << "Cand " << i << " (mix=" << c2_candidates[i].mix << "): "
              << "w0=" << w0 << ", w1=" << w1 << ", w2=" << w2 << ", w3=" << w3
              << " | min_w=" << std::min({w0, w1, w2, w3}) << "\n";
  }

  return 0;
}
