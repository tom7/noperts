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

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  // Basis in u0^perp
  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 2000);
  std::vector<double> angles;

  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      BigVecQ3 uc = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
      BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
      BigRat lam = dot / u0_sq;
      if (lam > 0) {
        BigVecQ3 w = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
        vec3 wf = {w.x.ToDouble(), w.y.ToDouble(), w.z.ToDouble()};
        double x = yocto::dot(wf, ex);
        double y = yocto::dot(wf, ey);
        double ang = std::atan2(y, x) * 180.0 / M_PI;
        angles.push_back(ang);
      }
    }
  }

  std::sort(angles.begin(), angles.end());
  std::cout << "Angles count: " << angles.size() << "\n";
  if (!angles.empty()) {
    std::cout << "Min angle: " << angles.front() << " deg, Max angle: " << angles.back() << " deg\n";
    std::cout << "Total span: " << (angles.back() - angles.front()) << " deg\n";
    // Check max gap between consecutive angles
    double max_gap = 0;
    for (size_t i = 0; i < angles.size() - 1; i++) {
      max_gap = std::max(max_gap, angles[i+1] - angles[i]);
    }
    max_gap = std::max(max_gap, 360.0 - (angles.back() - angles.front()));
    std::cout << "Max angular gap in u0^perp: " << max_gap << " deg\n";
  }
  return 0;
}
