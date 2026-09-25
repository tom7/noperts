#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  const auto &ax = axes[3449];
  ContactInfo base[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};

  vec3 a = yocto::normalize(vec3{0.3992, -0.4799, -0.7813});

  struct Res {
    int m[3];
    double del;
    double dot;
  };
  std::vector<Res> results;

  for (int m0 = 0; m0 <= 400; m0 += 100) {
    for (int m1 = 600; m1 <= 1000; m1 += 100) {
      for (int m2 = 400; m2 <= 1000; m2 += 100) {
        ContactInfo test[3] = {base[0], base[1], base[2]};
        test[0].mix = m0; test[1].mix = m1; test[2].mix = m2;

        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        std::string err;
        if (Tube229::AuditAxis(tri, test, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
          double B = cert.B.ToDouble();
          vec3 v = vec3{ctr.x.ToDouble() / B, ctr.y.ToDouble() / B, ctr.z.ToDouble() / B};
          results.push_back({{m0, m1, m2}, del.ToDouble(), yocto::dot(a, v)});
        }
      }
    }
  }

  std::sort(results.begin(), results.end(), [](const Res &r1, const Res &r2) {
    return r1.dot > r2.dot;
  });

  for (int i = 0; i < std::min(10, (int)results.size()); i++) {
    std::cout << "mix (" << results[i].m[0] << ", " << results[i].m[1] << ", " << results[i].m[2]
              << "): dot = " << results[i].dot << ", delta = " << results[i].del << "\n";
  }

  return 0;
}
