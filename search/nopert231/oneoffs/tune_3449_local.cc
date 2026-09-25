#include <iostream>
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

  double box_delta = 165676.0 / 1000000000.0;

  for (int m0 = 100; m0 <= 300; m0 += 20) {
    for (int m1 = 800; m1 <= 1000; m1 += 50) {
      for (int m2 = 600; m2 <= 1000; m2 += 50) {
        ContactInfo test[3] = {base[0], base[1], base[2]};
        test[0].mix = m0; test[1].mix = m1; test[2].mix = m2;

        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        std::string err;
        if (Tube229::AuditAxis(tri, test, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
          double B = cert.B.ToDouble();
          vec3 v = vec3{ctr.x.ToDouble() / B, ctr.y.ToDouble() / B, ctr.z.ToDouble() / B};
          double d = yocto::dot(a, v);
          if (del.ToDouble() <= box_delta && d >= box_delta) {
            std::cout << "FOUND! mix (" << m0 << ", " << m1 << ", " << m2 << "): delta = "
                      << del.ToDouble() << ", dot = " << d << "\n";
          }
        }
      }
    }
  }

  return 0;
}
