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
  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  double norm_u0 = std::sqrt(u0_sq.ToDouble());
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  int chosen[] = {3054, 119, 3063, 22, 24};
  std::vector<vec3> v;
  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  // Decompose each v_m into (lambda_m * u0_f + vx_m * ex + vy_m * ey)
  for (size_t m = 0; m < v.size(); m++) {
    double lam = yocto::dot(v[m], u0_f);
    double vx = yocto::dot(v[m], ex);
    double vy = yocto::dot(v[m], ey);
    double angle = std::atan2(vy, vx) * 180.0 / M_PI;
    std::cout << "Axis " << chosen[m] << ": lam = " << lam << ", (vx, vy) = (" << vx << ", " << vy
              << "), azimuth = " << angle << " deg\n";
  }

  // Check outer ring psi in [50 deg, 73 deg]
  // In the outer ring, for a point with azimuth phi:
  // dot(a, v_m) = cos(psi) * lam + sin(psi) * (vx * cos(phi) + vy * sin(phi))
  // We want to find for each phi in [0, 360 deg], max_m dot(a, v_m) >= 0.005 for ALL psi in [50, 73] deg!
  double min_ring_dot = 1e9;
  for (int iphi = 0; iphi < 360; iphi++) {
    double phi = iphi * M_PI / 180.0;
    double min_over_psi = 1e9;
    for (int ipsi = 50; ipsi <= 73; ipsi++) {
      double psi = ipsi * M_PI / 180.0;
      double cp = std::cos(psi);
      double sp = std::sin(psi);

      double max_m = -1e9;
      for (size_t m = 0; m < v.size(); m++) {
        double lam = yocto::dot(v[m], u0_f);
        double vx = yocto::dot(v[m], ex);
        double vy = yocto::dot(v[m], ey);
        double d = cp * lam + sp * (vx * std::cos(phi) + vy * std::sin(phi));
        if (d > max_m) max_m = d;
      }
      if (max_m < min_over_psi) min_over_psi = max_m;
    }
    if (min_over_psi < min_ring_dot) min_ring_dot = min_over_psi;
  }
  std::cout << "Min dot product over entire outer ring [50, 73 deg]: " << min_ring_dot << "\n";

  return 0;
}
