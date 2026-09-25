#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);

  vec3 E1 = vec3{1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = vec3{0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  // The 7 audited core axes
  ContactInfo core_contacts[7][3] = {
    // 0: Axis 25
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 800, 15}, {3, 2, 2, 1, 0, 2}},
    // 1: Axis 175
    {{2, 1, 1, 4, 0, 1}, {1, 4, 4, 8, 0, 4}, {15, 19, 19, 3, 500, 19}},
    // 2: Axis 221
    {{2, 1, 1, 4, 0, 1}, {4, 8, 8, 9, 800, 8}, {15, 19, 19, 3, 500, 19}},
    // 3: Axis 1772
    {{2, 1, 1, 4, 666, 1}, {1, 4, 4, 8, 800, 4}, {10, 15, 15, 19, 200, 15}},
    // 4: Axis 2180
    {{2, 1, 1, 4, 800, 1}, {1, 4, 4, 8, 1000, 4}, {10, 15, 15, 19, 333, 15}},
    // 5: Axis 2941
    {{3, 2, 2, 1, 0, 2}, {1, 4, 4, 8, 666, 4}, {10, 15, 15, 19, 333, 15}},
    // 6: Axis 2951
    {{3, 2, 2, 1, 0, 2}, {1, 4, 4, 8, 800, 4}, {10, 15, 15, 19, 333, 15}}
  };

  std::vector<Tube229::AuditedAxis> cores(7);
  for (int m = 0; m < 7; m++) {
    if (!Tube229::AuditAxis(tri, core_contacts[m], &cores[m].cert, &cores[m].center, &cores[m].delta, &err, BigRat(1, 1000))) {
      std::cerr << "Audit failed for core " << m << ": " << err << "\n";
      return 1;
    }
  }

  struct LeafTri {
    double x1, y1, x2, y2, x3, y3;
    int local_axis_id;
  };

  std::vector<LeafTri> leaves = {
    {-22,-22, 0,-22, 0,0, 0},
    {0,-22, 11,-22, 11,-11, 4},
    {11,-11, 22,-11, 22,0, 3},
    {11,-16.5, 16.5,-11, 11,-11, 5},
    {16.5,-16.5, 16.5,-11, 11,-16.5, 6},
    {0,0, 22,0, 22,22, 1},
    {0,-22, 22,0, 0,0, 5},
    {-22,-22, 22,22, -22,22, 2}
  };

  double min_dot_over_all = 1e9;
  for (size_t i = 0; i < leaves.size(); i++) {
    const auto &lf = leaves[i];
    const auto &ax = cores[lf.local_axis_id];
    vec3 v = vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                  ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                  ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    
    vec3 pts[3] = {
      P0 + lf.x1 * E1 + lf.y1 * E2,
      P0 + lf.x2 * E1 + lf.y2 * E2,
      P0 + lf.x3 * E1 + lf.y3 * E2
    };

    double min_lf = 1e9;
    for (int k = 0; k < 3; k++) {
      double d = yocto::dot(pts[k], v) / yocto::length(pts[k]);
      min_lf = std::min(min_lf, d);
    }
    std::cout << "Leaf " << i << " (core " << lf.local_axis_id << "): min normalized dot = "
              << std::setprecision(8) << min_lf
              << ", delta = " << ax.delta.ToDouble()
              << ", margin = " << (min_lf - ax.delta.ToDouble()) << "\n";
    min_dot_over_all = std::min(min_dot_over_all, min_lf);
  }

  std::cout << "GLOBAL min normalized dot = " << min_dot_over_all << "\n";
  return 0;
}
