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
  double c_core = 0.001; // target margin

  // Let's test a simple grid of boxes partition of [-1, 1] x [-1, 1]
  // For each box [x_min, x_max] x [y_min, y_max], is there an axis v with worst-case >= c_core?
  // Worst-case of a . v on [x_min, x_max] x [y_min, y_max] x [c_cone, 1] with v = c1 k1 + c2 k2 + c0 u0 (c0 >= 0):
  // min_val = (c1 >= 0 ? c1 * x_min : c1 * x_max) + (c2 >= 0 ? c2 * y_min : c2 * y_max) + c0 * c_cone.

  auto test_grid = [&](int N) {
    int total_boxes = 0;
    int covered_boxes = 0;
    double step = 2.0 / N;
    for (int i = 0; i < N; i++) {
      double x_min = -1.0 + i * step;
      double x_max = -1.0 + (i + 1) * step;
      for (int j = 0; j < N; j++) {
        double y_min = -1.0 + j * step;
        double y_max = -1.0 + (j + 1) * step;

        // Check if box intersects the unit disk x^2 + y^2 <= 1
        // Closest point to origin in [x_min, x_max] x [y_min, y_max]:
        double cx = std::max(0.0, std::max(x_min, -x_max));
        double cy = std::max(0.0, std::max(y_min, -y_max));
        if (cx * cx + cy * cy > 1.0) continue; // outside disk

        total_boxes++;
        bool ok = false;
        for (const auto &ax : axes) {
          ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
          AxisCertificate cert; BigVecQ3 ctr; BigRat del;
          Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
          vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
          double c1 = yocto::dot(v, k1);
          double c2 = yocto::dot(v, k2);
          double c0 = yocto::dot(v, u0);
          if (c0 < 0) continue; // need c0 >= 0 for box_axis_cover

          double corner = (c1 >= 0 ? c1 * x_min : c1 * x_max) +
                          (c2 >= 0 ? c2 * y_min : c2 * y_max) +
                          c0 * c_cone;
          if (corner >= c_core) {
            ok = true;
            break;
          }
        }
        if (ok) covered_boxes++;
      }
    }
    std::cout << "Grid " << N << "x" << N << ": covered " << covered_boxes << " / " << total_boxes << " boxes\n";
  };

  test_grid(2);
  test_grid(4);
  test_grid(8);
  test_grid(16);
  return 0;
}
