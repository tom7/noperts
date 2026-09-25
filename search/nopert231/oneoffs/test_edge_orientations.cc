#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  BigVecQ3 c2 = tri1.corners[2];
  TriangleQ tri_c2;
  tri_c2.corners[0] = c2;
  tri_c2.corners[1] = c2;
  tri_c2.corners[2] = c2;

  vec3 uncov = yocto::normalize(vec3{0.401011, -0.483067, -0.778355});

  std::cout << std::setprecision(10);
  for (bool rev0 : {false, true}) {
    for (bool rev1 : {false, true}) {
      for (bool rev2 : {false, true}) {
        int e0_s = rev0 ? 3 : 19, e0_f = rev0 ? 19 : 3;
        int e1_s = rev1 ? 8 : 4,  e1_f = rev1 ? 4 : 8;
        int e2_s = rev2 ? 15 : 10, e2_f = rev2 ? 10 : 15;

        ContactInfo triple[3] = {
          {e0_s, e0_f, e0_s, e0_f, 1000, 19},
          {e1_s, e1_f, e1_s, e1_f, 1000, 4},
          {e2_s, e2_f, e2_s, e2_f, 1000, 15}
        };

        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri_c2, triple, &cand, 1e-12)) {
          double d = yocto::dot(cand.normalized_a, uncov);
          std::cout << "Reversals (" << rev0 << rev1 << rev2 << "): "
                    << "norm_a = (" << cand.normalized_a.x << ", "
                    << cand.normalized_a.y << ", " << cand.normalized_a.z << ")"
                    << " | dot(a, uncov) = " << d
                    << " | slack = " << cand.strict_slack << "\n";
        }
      }
    }
  }

  return 0;
}
