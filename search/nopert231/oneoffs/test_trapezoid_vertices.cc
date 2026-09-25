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
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  struct AxisData {
    int idx;
    double lam;
    double vx, vy;
    vec3 v;
  };
  std::vector<AxisData> zd_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      double lam = yocto::dot(v, u0_f);
      double vx = yocto::dot(v, ex);
      double vy = yocto::dot(v, ey);
      zd_axes.push_back({(int)i, lam, vx, vy, v});
    }
  }

  // Ring angles:
  // Inner: psi_in = 50 deg
  // Outer: psi_out = 73 deg
  double psi_in = 50.0 * M_PI / 180.0;
  double psi_out = 73.0 * M_PI / 180.0;

  // Let's divide azimuth [0, 360) into S sectors:
  for (int S : {8, 12, 16}) {
    std::cout << "Testing S = " << S << " sectors:\n";
    bool all_sectors_covered = true;
    for (int s = 0; s < S; s++) {
      double phi1 = s * 2.0 * M_PI / S;
      double phi2 = (s + 1) * 2.0 * M_PI / S;

      // 4 vertices of the trapezoid:
      vec3 V[4] = {
        std::cos(psi_in) * u0_f + std::sin(psi_in) * (std::cos(phi1) * ex + std::sin(phi1) * ey),
        std::cos(psi_in) * u0_f + std::sin(psi_in) * (std::cos(phi2) * ex + std::sin(phi2) * ey),
        std::cos(psi_out) * u0_f + std::sin(psi_out) * (std::cos(phi1) * ex + std::sin(phi1) * ey),
        std::cos(psi_out) * u0_f + std::sin(psi_out) * (std::cos(phi2) * ex + std::sin(phi2) * ey)
      };

      // Find an axis where min_{k=0..3} dot(V[k], v) is maximized
      double best_min_dot = -1e9;
      int best_idx = -1;
      for (const auto &ax : zd_axes) {
        double min_dot = 1e9;
        for (int k = 0; k < 4; k++) {
          double d = yocto::dot(V[k], ax.v);
          if (d < min_dot) min_dot = d;
        }
        if (min_dot > best_min_dot) {
          best_min_dot = min_dot;
          best_idx = ax.idx;
        }
      }

      if (best_min_dot < 0.005) {
        all_sectors_covered = false;
        std::cout << "  Sector " << s << " [" << (phi1*180/M_PI) << ", " << (phi2*180/M_PI)
                  << "] failed: best min dot = " << best_min_dot << "\n";
      } else {
        std::cout << "  Sector " << s << " [" << (phi1*180/M_PI) << ", " << (phi2*180/M_PI)
                  << "] covered by Axis " << best_idx << " with min dot = " << best_min_dot << "\n";
      }
    }
    if (all_sectors_covered) {
      std::cout << "SUCCESS for S = " << S << "!\n";
      return 0;
    }
  }

  return 0;
}
