#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  vec3 n_seam = yocto::normalize(vec3{0.237066, -0.757116, -0.182676});
  vec3 u_c2 = yocto::normalize(vec3{0.91602049, 0.20340275, 0.34573659});

  std::cout << "Seam normal: (" << n_seam.x << ", " << n_seam.y << ", " << n_seam.z << ")\n";
  std::cout << "Corner 2 view: dot_seam = " << yocto::dot(u_c2, n_seam) << "\n";

  // Let's test points on the eclipsed side: dot_seam > 0
  for (double dist : {0.020, 0.022, 0.024, 0.026, 0.028, 0.030, 0.032, 0.035}) {
    vec3 u_ecl = yocto::normalize(u_c2 + dist * n_seam);
    double dot = yocto::dot(u_ecl, n_seam);

    // Can we find a balanced tetrahedron at this view?
    // We construct a small degenerate or tiny triangle around u_ecl
    BigRat bx = BigRat::FromDouble(u_ecl.x);
    BigRat by = BigRat::FromDouble(u_ecl.y);
    BigRat bz = BigRat::FromDouble(u_ecl.z);
    TriangleQ tri_pt = {
      BigVecQ3{bx, by, bz},
      BigVecQ3{bx, by, bz},
      BigVecQ3{bx, by, bz}
    };

    auto cands = Tube229::GenerateCandidatesForView(u_ecl, tri_pt, false);
    std::vector<vec3> cand_centers;
    for (const auto &c : cands) cand_centers.push_back(c.normalized_a);

    std::array<int, 4> simplex;
    vec3 sep;
    bool caged = Tube229::FindBalancedTetrahedron(cand_centers, &simplex, &sep);
    std::cout << "dist=" << std::setw(8) << dist
              << " dot=" << std::setw(11) << dot
              << " cands=" << std::setw(4) << cands.size()
              << " caged=" << (caged ? "YES" : "NO")
              << " sep_norm=" << yocto::length(sep) << "\n";
    if (caged) {
      std::cout << "  Caging simplex indices: " << simplex[0] << ", " << simplex[1]
                << ", " << simplex[2] << ", " << simplex[3] << "\n";
      for (int m = 0; m < 4; m++) {
        const auto &ct = cands[simplex[m]];
        std::cout << "    Axis " << m << " contacts: ("
                  << ct.contacts[0].vertex << ", "
                  << ct.contacts[1].vertex << ", "
                  << ct.contacts[2].vertex << ")\n";
      }
    }
  }

  return 0;
}
