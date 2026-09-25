#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  const auto &ax = axes[3449];
  ContactInfo tuned_info[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
  tuned_info[0].mix = 0;
  tuned_info[1].mix = 0;
  tuned_info[2].mix = 500;

  AxisCertificate cert;
  BigVecQ3 ctr;
  BigRat del;
  std::string err;
  Tube229::AuditAxis(tri, tuned_info, &cert, &ctr, &del, &err, BigRat(1, 1000));

  double B = cert.B.ToDouble();
  vec3 v = vec3{ctr.x.ToDouble() / B, ctr.y.ToDouble() / B, ctr.z.ToDouble() / B};

  vec3 a1 = yocto::normalize(vec3{0.39639, -0.49234, -0.77493});
  vec3 a2 = yocto::normalize(vec3{0.3992, -0.4799, -0.7813});

  std::cout << "Tuned 3449 delta = " << del.ToDouble() << "\n";
  std::cout << "dot with a1 = " << yocto::dot(a1, v) << "\n";
  std::cout << "dot with a2 = " << yocto::dot(a2, v) << "\n";

  return 0;
}
