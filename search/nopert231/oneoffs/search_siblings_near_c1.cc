#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  vec3 c1 = yocto::normalize(vec3{0.3992, -0.494824, -0.771874});

  // Let us test various contact triples near ax0:
  // ax0 contacts: {3, 2, 800, 2}, {1, 4, 800, 4}, {e3, e4, mix, v}
  // Try all edges e3 for the third contact!
  std::cout << "Testing variations of third contact near ax0:\n";

  double best_d = -1.0;
  ContactInfo best_c[3];
  AxisCertificate best_ax;
  BigRat best_del;

  for (int e3 = 0; e3 < 60; e3++) {
    for (int mix = 0; mix <= 1000; mix += 200) {
      ContactInfo c[3] = {
        {3, 2, 2, 1, 800, 2},
        {1, 4, 4, 8, 800, 4},
        {e3, (e3 + 1) % 60, (e3 + 1) % 60, (e3 + 2) % 60, mix, e3 % 24}
      };
      AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
      if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
        double B = ax.B.ToDouble();
        vec3 v = vec3{ctr.x.ToDouble() / B, ctr.y.ToDouble() / B, ctr.z.ToDouble() / B};
        double d = yocto::dot(c1, v);
        if (d > 0.005 && del.ToDouble() <= 0.000235) {
          std::cout << "  e3=" << e3 << ", mix=" << mix << ": dot=" << d
                    << ", delta=" << del.ToDouble() << ", B=" << B << "\n";
        }
      }
    }
  }

  return 0;
}
