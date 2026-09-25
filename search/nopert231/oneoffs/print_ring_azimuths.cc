#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  int chosen[] = {3054, 119, 3063, 22, 24};
  std::vector<vec3> v;
  std::string err2;
  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err2, BigRat(0));
    v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  // For each integer degree phi from -180 to 180:
  // find which axis m gives dot >= 0.005 for all psi in [50, 73]
  for (int deg = -180; deg < 180; deg += 10) {
    double phi = deg * M_PI / 180.0;
    std::cout << "phi = " << deg << " deg: ";
    for (size_t m = 0; m < v.size(); m++) {
      double min_d = 1e9;
      for (int ipsi = 50; ipsi <= 73; ipsi++) {
        double psi = ipsi * M_PI / 180.0;
        double cp = std::cos(psi);
        double sp = std::sin(psi);
        double lam = yocto::dot(v[m], u0_f);
        double vx = yocto::dot(v[m], ex);
        double vy = yocto::dot(v[m], ey);
        double d = cp * lam + sp * (vx * std::cos(phi) + vy * std::sin(phi));
        if (d < min_d) min_d = d;
      }
      if (min_d >= 0.005) {
        std::cout << chosen[m] << "(" << min_d << ") ";
      }
    }
    std::cout << "\n";
  }

  return 0;
}
