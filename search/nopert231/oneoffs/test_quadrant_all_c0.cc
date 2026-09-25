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

  double c_cone = 0.015;
  double c_core = 0.001;

  struct PrecomputedAxis {
    double c1, c2, c0;
    int v0, v1, v2;
  };
  std::vector<PrecomputedAxis> audited;
  for (const auto &ax : axes) {
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    audited.push_back({yocto::dot(v, k1), yocto::dot(v, k2), yocto::dot(v, u0),
                       ax.cert.contacts[0].vertex, ax.cert.contacts[1].vertex, ax.cert.contacts[2].vertex});
  }

  // Check 4 quadrants
  // Q0: [0, 1] x [0, 1]
  // Q1: [-1, 0] x [0, 1]
  // Q2: [-1, 0] x [-1, 0]
  // Q3: [0, 1] x [-1, 0]
  double quads[4][4] = {
    {0, 1, 0, 1},
    {-1, 0, 0, 1},
    {-1, 0, -1, 0},
    {0, 1, -1, 0}
  };

  for (int q = 0; q < 4; q++) {
    double x_min = quads[q][0], x_max = quads[q][1];
    double y_min = quads[q][2], y_max = quads[q][3];
    double best_corner = -1e9;
    int best_ax = -1;
    for (size_t i = 0; i < audited.size(); i++) {
      double c1 = audited[i].c1;
      double c2 = audited[i].c2;
      double c0 = audited[i].c0;
      double term_u = (c0 >= 0) ? (c0 * c_cone) : (c0 * 1.0);
      double corner = (c1 >= 0 ? c1 * x_min : c1 * x_max) +
                      (c2 >= 0 ? c2 * y_min : c2 * y_max) +
                      term_u;
      if (corner > best_corner) {
        best_corner = corner;
        best_ax = i;
      }
    }
    std::cout << "Quadrant " << q << ": best_corner = " << best_corner
              << " (axis " << best_ax << " contacts "
              << audited[best_ax].v0 << "," << audited[best_ax].v1 << "," << audited[best_ax].v2 << ")\n";
  }
  return 0;
}
