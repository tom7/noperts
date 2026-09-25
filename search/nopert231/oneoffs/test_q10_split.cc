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

  // Split Quadrant [1,0] (x in [0, R], y in [-R, 0]) into M x M sub-boxes
  for (int M : {2, 3, 4, 5, 6, 8}) {
    double step = R / M;
    int covered = 0, total = 0;
    for (int ix = 0; ix < M; ix++) {
      double x_min = ix * step;
      double x_max = (ix + 1) * step;
      for (int iy = 0; iy < M; iy++) {
        double y_min = -R + iy * step;
        double y_max = -R + (iy + 1) * step;

        double cx = (0 >= x_min && 0 <= x_max) ? 0 : std::min(std::abs(x_min), std::abs(x_max));
        double cy = (0 >= y_min && 0 <= y_max) ? 0 : std::min(std::abs(y_min), std::abs(y_max));
        if (cx * cx + cy * cy > R * R) continue;

        total++;
        double best_margin = -1e9;
        int best_ax = -1;

        for (size_t i = 0; i < all_v.size(); i++) {
          vec3 v = all_v[i];
          double c1 = yocto::dot(v, k1);
          double c2 = yocto::dot(v, k2);
          double c0_u0 = yocto::dot(v, u0);

          double w1 = (c1 >= 0 ? c1 * x_min : c1 * x_max);
          double w2 = (c2 >= 0 ? c2 * y_min : c2 * y_max);
          double w0 = (c0_u0 >= 0 ? c0_u0 * cos_alpha : c0_u0 * 1.0);
          double margin = w1 + w2 + w0;
          if (margin > best_margin) {
            best_margin = margin;
            best_ax = i;
          }
        }
        if (best_margin >= 0.001) covered++;
      }
    }
    std::cout << "M = " << M << ": " << covered << " / " << total << " sub-boxes covered in Quadrant [1,0]\n";
  }

  return 0;
}
