#include <iostream>
#include <iomanip>
#include <cmath>
#include <algorithm>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  // Certificate axes 0, 1, 2, 3 from sibling n0:
  ContactInfo ax0[3] = { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14} };
  ContactInfo ax1[3] = { {15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9} };
  ContactInfo ax2[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15} };
  ContactInfo ax3[3] = { {3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15} };

  Tube229::CandidateTriple cand[4];
  Tube229::DoubleCheckAxis(tri1, ax0, &cand[0], 1e-5);
  Tube229::DoubleCheckAxis(tri1, ax1, &cand[1], 0.0);
  Tube229::DoubleCheckAxis(tri1, ax2, &cand[2], 0.0);
  Tube229::DoubleCheckAxis(tri1, ax3, &cand[3], 0.0);

  vec3 u0 = cand[0].normalized_a;
  vec3 u1 = cand[1].normalized_a;
  vec3 u2 = cand[2].normalized_a;
  vec3 u3 = cand[3].normalized_a;

  std::cout << "Normalized axes:\n";
  std::cout << "  u0: (" << u0.x << ", " << u0.y << ", " << u0.z << "), len=" << yocto::length(u0) << "\n";
  std::cout << "  u1: (" << u1.x << ", " << u1.y << ", " << u1.z << "), len=" << yocto::length(u1) << "\n";
  std::cout << "  u2: (" << u2.x << ", " << u2.y << ", " << u2.z << "), len=" << yocto::length(u2) << "\n";
  std::cout << "  u3: (" << u3.x << ", " << u3.y << ", " << u3.z << "), len=" << yocto::length(u3) << "\n";

  vec3 un0 = yocto::normalize(u0);

  // Check on a dense Fibonacci sphere of 100,000 points
  int N = 200000;
  double phi = (1.0 + std::sqrt(5.0)) / 2.0;

  // Let's test different cone thresholds cos_cone around un0
  std::vector<double> cone_cos_thresholds = {
    0.80, 0.70, 0.60, 0.50, 0.40, 0.30, 0.20, 0.10, 0.0, -0.10, -0.50
  };

  for (double c_thresh : cone_cos_thresholds) {
    double min_sibling_margin = 1e30;
    vec3 worst_v = {0,0,0};

    for (int i = 0; i < N; i++) {
      double y = 1.0 - (i / (double)(N - 1)) * 2.0;
      double radius = std::sqrt(std::max(0.0, 1.0 - y * y));
      double theta = 2.0 * M_PI * i / phi;
      vec3 v = {std::cos(theta) * radius, y, std::sin(theta) * radius};

      // Is v inside the exceptional cone around un0?
      double dot0 = yocto::dot(v, un0);
      if (dot0 >= c_thresh) {
        continue; // inside cone, skip
      }

      // Outside cone: what is max projection onto sibling axes?
      // Note: in local certificate, the projection is dot(v, u_j)
      double m1 = yocto::dot(v, u1);
      double m2 = yocto::dot(v, u2);
      double m3 = yocto::dot(v, u3);
      double max_m = std::max({m1, m2, m3});

      if (max_m < min_sibling_margin) {
        min_sibling_margin = max_m;
        worst_v = v;
      }
    }

    std::cout << "For c_cone = " << c_thresh << ": min sibling margin = "
              << min_sibling_margin << " at worst_v = ("
              << worst_v.x << ", " << worst_v.y << ", " << worst_v.z << ")\n";
  }

  return 0;
}
