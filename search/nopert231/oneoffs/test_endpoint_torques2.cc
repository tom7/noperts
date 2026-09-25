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

  int e_s[3] = {19, 4, 10};
  int e_f[3] = {3, 8, 15};

  vec3 uncov = yocto::normalize(vec3{0.401011, -0.483067, -0.778355});

  std::cout << std::setprecision(10);
  for (int p0 : {19, 3}) {
    for (int p1 : {4, 8}) {
      for (int p2 : {10, 15}) {
        ContactInfo triple[3] = {
          {e_s[0], e_f[0], e_s[0], e_f[0], 1000, p0},
          {e_s[1], e_f[1], e_s[1], e_f[1], 1000, p1},
          {e_s[2], e_f[2], e_s[2], e_f[2], 1000, p2}
        };
        Tube229::CandidateTriple cand;
        bool ok = Tube229::DoubleCheckAxis(tri_c2, triple, &cand, 1e-12);
        if (ok) {
          double d = yocto::dot(cand.normalized_a, uncov);
          std::cout << "Vertices (" << p0 << ", " << p1 << ", " << p2 << "): "
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
