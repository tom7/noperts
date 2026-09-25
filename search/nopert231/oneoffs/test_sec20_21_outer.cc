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

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  auto get_v = [&](int idx) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    return yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
  };

  vec3 v22 = get_v(22);
  vec3 v119 = get_v(119);
  vec3 v24 = get_v(24);

  // Check sector 20: phi in [300, 315], psi in [55, 73]
  // Check sector 21: phi in [315, 330], psi in [55, 73]
  auto eval_box = [&](double phi1, double phi2, double psi1, double psi2, vec3 v, const std::string &name) {
    double p1 = phi1*M_PI/180.0, p2 = phi2*M_PI/180.0;
    double s1 = psi1*M_PI/180.0, s2 = psi2*M_PI/180.0;
    vec3 pts[4] = {
      std::cos(s1)*u0 + std::sin(s1)*(std::cos(p1)*ex + std::sin(p1)*ey),
      std::cos(s1)*u0 + std::sin(s1)*(std::cos(p2)*ex + std::sin(p2)*ey),
      std::cos(s2)*u0 + std::sin(s2)*(std::cos(p1)*ex + std::sin(p1)*ey),
      std::cos(s2)*u0 + std::sin(s2)*(std::cos(p2)*ex + std::sin(p2)*ey)
    };
    std::cout << name << " on phi[" << phi1 << "," << phi2 << "] psi[" << psi1 << "," << psi2 << "]:\n";
    for (int i = 0; i < 4; i++) {
      std::cout << "  pt " << i << ": dot = " << yocto::dot(pts[i], v) << "\n";
    }
  };

  eval_box(300, 315, 55, 73, v22, "Axis 22");
  eval_box(315, 330, 55, 73, v22, "Axis 22");
  eval_box(315, 330, 55, 73, v119, "Axis 119");

  return 0;
}
