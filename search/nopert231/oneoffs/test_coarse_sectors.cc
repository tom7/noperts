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

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    auto &ax = axes[i];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    all_v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  double s1 = 51.51 * M_PI / 180.0;
  double s2 = 72.93 * M_PI / 180.0;

  for (int num_sec : {4, 6, 8, 12, 16}) {
    double dphi = 360.0 / num_sec;
    int ok_count = 0;
    for (int s = 0; s < num_sec; s++) {
      double p1 = (s * dphi) * M_PI / 180.0;
      double p2 = ((s + 1) * dphi) * M_PI / 180.0;
      vec3 p00 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p1)*ex + std::sin(p1)*ey);
      vec3 p01 = std::cos(s1)*u0 + std::sin(s1)*(std::cos(p2)*ex + std::sin(p2)*ey);
      vec3 p10 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p1)*ex + std::sin(p1)*ey);
      vec3 p11 = std::cos(s2)*u0 + std::sin(s2)*(std::cos(p2)*ex + std::sin(p2)*ey);

      int a1_ax = -1, a2_ax = -1, b1_ax = -1, b2_ax = -1;
      for (size_t i = 0; i < all_v.size(); i++) {
        vec3 v = all_v[i];
        if (yocto::dot(p00, v) > 0.001 && yocto::dot(p01, v) > 0.001 && yocto::dot(p11, v) > 0.001) a1_ax = i;
        if (yocto::dot(p00, v) > 0.001 && yocto::dot(p10, v) > 0.001 && yocto::dot(p11, v) > 0.001) a2_ax = i;
        if (yocto::dot(p00, v) > 0.001 && yocto::dot(p01, v) > 0.001 && yocto::dot(p10, v) > 0.001) b1_ax = i;
        if (yocto::dot(p01, v) > 0.001 && yocto::dot(p10, v) > 0.001 && yocto::dot(p11, v) > 0.001) b2_ax = i;
      }
      if ((a1_ax >= 0 && a2_ax >= 0) || (b1_ax >= 0 && b2_ax >= 0)) ok_count++;
    }
    std::cout << num_sec << " sectors (dphi = " << dphi << " deg): " << ok_count << " / " << num_sec << " certified\n";
  }

  return 0;
}
