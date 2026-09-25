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
  BigVecQ3 u0_q = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  vec3 u0 = {u0_q.x.ToDouble(), u0_q.y.ToDouble(), u0_q.z.ToDouble()};
  double c_cone = 0.015;

  std::vector<vec3> zd_axes;
  std::vector<int> zd_idx;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      zd_axes.push_back(v);
      zd_idx.push_back((int)i);
    }
  }
  std::cout << "Zero defect axes: " << zd_axes.size() << "\n";

  for (int G : {4, 6, 8, 10, 12}) {
    std::vector<double> grid(G + 1);
    for (int i = 0; i <= G; i++) {
      grid[i] = -1.0 + 2.0 * i / G;
    }

    int total_boxes = G * G * G;
    int disc_outside_sphere = 0;
    int disc_outside_cone = 0;
    int covered_by_axis = 0;
    int unsolved = 0;

    for (int ix = 0; ix < G; ix++) {
      double x1 = grid[ix], x2 = grid[ix+1];
      for (int iy = 0; iy < G; iy++) {
        double y1 = grid[iy], y2 = grid[iy+1];
        for (int iz = 0; iz < G; iz++) {
          double z1 = grid[iz], z2 = grid[iz+1];

          // Check if box intersects unit sphere:
          // Min distance squared from origin to box:
          double min_x = (x1 <= 0 && x2 >= 0) ? 0 : std::min(std::abs(x1), std::abs(x2));
          double min_y = (y1 <= 0 && y2 >= 0) ? 0 : std::min(std::abs(y1), std::abs(y2));
          double min_z = (z1 <= 0 && z2 >= 0) ? 0 : std::min(std::abs(z1), std::abs(z2));
          double min_r2 = min_x * min_x + min_y * min_y + min_z * min_z;

          double max_x = std::max(std::abs(x1), std::abs(x2));
          double max_y = std::max(std::abs(y1), std::abs(y2));
          double max_z = std::max(std::abs(z1), std::abs(z2));
          double max_r2 = max_x * max_x + max_y * max_y + max_z * max_z;

          if (min_r2 > 1.0 || max_r2 < 1.0) {
            disc_outside_sphere++;
            continue;
          }

          // Check if box can be proven outside the cone:
          // max_{a in box} (a . u0) < c_cone
          double max_dot_u0 = (u0.x >= 0 ? u0.x * x2 : u0.x * x1) +
                              (u0.y >= 0 ? u0.y * y2 : u0.y * y1) +
                              (u0.z >= 0 ? u0.z * z2 : u0.z * z1);
          if (max_dot_u0 < c_cone) {
            disc_outside_cone++;
            continue;
          }

          // Check if any zero defect axis achieves min_{a in box} (a . v) >= c_core
          double best_bound = -1e9;
          for (const auto &v : zd_axes) {
            double min_dot_v = (v.x >= 0 ? v.x * x1 : v.x * x2) +
                               (v.y >= 0 ? v.y * y1 : v.y * y2) +
                               (v.z >= 0 ? v.z * z1 : v.z * z2);
            if (min_dot_v > best_bound) best_bound = min_dot_v;
          }

          if (best_bound >= 0.001) {
            covered_by_axis++;
          } else {
            unsolved++;
          }
        }
      }
    }

    std::cout << "Grid " << G << "^3 = " << total_boxes << ": "
              << disc_outside_sphere << " out sphere, "
              << disc_outside_cone << " out cone, "
              << covered_by_axis << " covered, "
              << unsolved << " unsolved\n";
  }

  return 0;
}
