#include <iostream>
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
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  int chosen[] = {3063, 22, 24, 3054, 119};
  std::vector<vec3> v;
  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  // Check on the entire 2D grid of (psi, phi):
  // psi in [0, 73 deg] with step 1 deg
  // phi in [0, 360 deg] with step 1 deg
  double min_overall = 1e9;
  for (int ipsi = 0; ipsi <= 73; ipsi++) {
    double psi = ipsi * M_PI / 180.0;
    for (int iphi = 0; iphi < 360; iphi++) {
      double phi = iphi * M_PI / 180.0;
      vec3 pt = std::cos(psi) * u0_f + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey);
      double max_dot = -1e9;
      for (size_t m = 0; m < v.size(); m++) {
        double d = yocto::dot(pt, v[m]);
        if (d > max_dot) max_dot = d;
      }
      if (max_dot < min_overall) min_overall = max_dot;
    }
  }
  std::cout << "Exact 5-axis flock minimum over ALL (psi, phi) in [0, 73] x [0, 360]: "
            << min_overall << "\n";

  return 0;
}
