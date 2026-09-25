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

  struct AxisData {
    int idx;
    double lam;
    double vx, vy;
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
      zd_axes.push_back({(int)i, lam, vx, vy});
    }
  }

  double c_cone = 0.015;
  double z_cone_min = c_cone / norm_u0;
  double r_disk = std::sqrt(std::max(0.0, 1.0 - z_cone_min * z_cone_min));

  for (int G : {14, 16, 18, 20}) {
    std::vector<double> grid(G + 1);
    for (int i = 0; i <= G; i++) {
      grid[i] = -1.0 + 2.0 * i / G;
    }

    int total_boxes = 0;
    int covered_boxes = 0;
    double min_box_bound = 1e9;

    for (int i = 0; i < G; i++) {
      double x1 = grid[i], x2 = grid[i+1];
      for (int j = 0; j < G; j++) {
        double y1 = grid[j], y2 = grid[j+1];

        double closest_x = std::max(0.0, std::max(x1, -x2));
        if (x1 <= 0 && x2 >= 0) closest_x = 0;
        double closest_y = std::max(0.0, std::max(y1, -y2));
        if (y1 <= 0 && y2 >= 0) closest_y = 0;

        if (closest_x * closest_x + closest_y * closest_y > r_disk * r_disk) {
          continue;
        }
        total_boxes++;

        double far_x = std::max(std::abs(x1), std::abs(x2));
        double far_y = std::max(std::abs(y1), std::abs(y2));
        double far_r2 = far_x * far_x + far_y * far_y;

        double z_min = z_cone_min;
        if (far_r2 < 1.0) {
          z_min = std::max(z_min, std::sqrt(1.0 - far_r2));
        }
        double z_max = 1.0;
        double near_r2 = closest_x * closest_x + closest_y * closest_y;
        if (near_r2 < 1.0) {
          z_max = std::sqrt(1.0 - near_r2);
        }

        double best_lower_bound = -1e9;
        for (const auto &ax : zd_axes) {
          double z_term = (ax.lam >= 0) ? (ax.lam * z_min) : (ax.lam * z_max);
          double x_term = std::min(ax.vx * x1, ax.vx * x2);
          double y_term = std::min(ax.vy * y1, ax.vy * y2);
          double lower_bound = z_term + x_term + y_term;
          if (lower_bound > best_lower_bound) {
            best_lower_bound = lower_bound;
          }
        }

        if (best_lower_bound >= 0.001) {
          covered_boxes++;
          if (best_lower_bound < min_box_bound) min_box_bound = best_lower_bound;
        }
      }
    }

    std::cout << "Grid " << G << "x" << G << ": " << covered_boxes << " / " << total_boxes
              << " boxes covered (min bound = " << min_box_bound << ")\n";
  }

  return 0;
}
