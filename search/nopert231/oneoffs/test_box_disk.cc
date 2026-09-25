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
  vec3 u0_raw = vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    auto &ax = axes[i];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    all_v.push_back(yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()}));
  }

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double R = std::sqrt(std::max(0.0, 1.0 - cos_alpha * cos_alpha));

  // In Quadrant [1,0]: x in [0, R], y in [-R, 0].
  // The disk sector in this quadrant is: x in [0, R], y in [-R, 0], x^2 + y^2 <= R^2.
  // Can we cover this sector with 2 or 3 triangles or boxes?
  // Let's test a triangle partition of the disk sector:
  // Points: Origin O = (0,0)
  // Arc points at angle theta from -pi/2 to 0:
  for (int S : {2, 3, 4, 5, 6}) {
    double dth = (M_PI / 2.0) / S;
    bool all_sectors_covered = true;
    for (int s = 0; s < S; s++) {
      double th1 = -M_PI / 2.0 + s * dth;
      double th2 = -M_PI / 2.0 + (s + 1) * dth;
      vec3 p1 = R * std::cos(th1) * k1 + R * std::sin(th1) * k2 + cos_alpha * u0;
      vec3 p2 = R * std::cos(th2) * k1 + R * std::sin(th2) * k2 + cos_alpha * u0;
      vec3 p0 = 1.0 * u0; // cone apex

      // An axis covers this spherical triangle if dot(v, p) >= 0.001 for p in {p0, p1, p2}
      int best_ax = -1;
      double best_margin = -1e9;
      for (size_t i = 0; i < all_v.size(); i++) {
        vec3 v = all_v[i];
        double m0 = yocto::dot(v, p0);
        double m1 = yocto::dot(v, p1);
        double m2 = yocto::dot(v, p2);
        double m = std::min({m0, m1, m2});
        if (m > best_margin) {
          best_margin = m;
          best_ax = i;
        }
      }
      if (best_margin < 0.001) {
        all_sectors_covered = false;
        std::cout << "S=" << S << " sector " << s << " FAILED (margin " << best_margin << ")\n";
      } else {
        std::cout << "S=" << S << " sector " << s << " COVERED by axis " << best_ax << " (margin " << best_margin << ")\n";
      }
    }
    if (all_sectors_covered) {
      std::cout << "===> S=" << S << " FULLY COVERS QUADRANT [1,0]!\n";
      break;
    }
  }

  return 0;
}
