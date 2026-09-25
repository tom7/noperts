#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  auto get_v = [&](int idx) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    return yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
  };

  vec3 v_3063 = get_v(3063);
  vec3 v_213 = get_v(213);
  vec3 v_25 = get_v(25);

  double phi = 315.0 * M_PI / 180.0;
  for (int psi_deg = 45; psi_deg <= 75; psi_deg++) {
    double psi = psi_deg * M_PI / 180.0;
    vec3 pt = std::sin(psi) * (std::cos(phi) * k1 + std::sin(phi) * k2) + std::cos(psi) * u0;
    std::cout << "psi=" << psi_deg << ": "
              << "dot(3063)=" << yocto::dot(v_3063, pt) << ", "
              << "dot(213)=" << yocto::dot(v_213, pt) << ", "
              << "dot(25)=" << yocto::dot(v_25, pt) << ", "
              << "MAX=" << std::max({yocto::dot(v_3063, pt), yocto::dot(v_213, pt), yocto::dot(v_25, pt)}) << "\n";
  }
  return 0;
}
