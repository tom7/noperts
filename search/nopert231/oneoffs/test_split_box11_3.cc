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
  double norm_u0 = std::sqrt((u0.x * u0.x + u0.y * u0.y + u0.z * u0.z).ToDouble());
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
  double z_split = std::cos(51.7 * M_PI / 180.0);
  double r_inner = std::sqrt(1.0 - z_split * z_split);
  double r_outer = std::sqrt(1.0 - z_cone_min * z_cone_min);

  // Split Box (11, 3) into 2x2 subboxes:
  double x_mids[3] = {0.571429, (0.571429 + 0.714286) / 2.0, 0.714286};
  double y_mids[3] = {-0.571429, (-0.571429 - 0.428571) / 2.0, -0.428571};

  std::cout << "Testing 2x2 split of Box (11, 3):\n";
  for (int si = 0; si < 2; si++) {
    for (int sj = 0; sj < 2; sj++) {
      double x1 = x_mids[si], x2 = x_mids[si+1];
      double y1 = y_mids[sj], y2 = y_mids[sj+1];

      double closest_x = (x1 <= 0 && x2 >= 0) ? 0 : std::min(std::abs(x1), std::abs(x2));
      double closest_y = (y1 <= 0 && y2 >= 0) ? 0 : std::min(std::abs(y1), std::abs(y2));
      double near_r2 = closest_x * closest_x + closest_y * closest_y;

      double far_x = std::max(std::abs(x1), std::abs(x2));
      double far_y = std::max(std::abs(y1), std::abs(y2));
      double far_r2 = far_x * far_x + far_y * far_y;

      if (near_r2 > r_outer * r_outer) {
        std::cout << "Subbox (" << si << ", " << sj << ") completely outside cone\n";
        continue;
      }
      if (far_r2 < r_inner * r_inner) {
        std::cout << "Subbox (" << si << ", " << sj << ") completely inside inner disk (covered by 3063)\n";
        continue;
      }

      double z_min = z_cone_min;
      if (far_r2 < 1.0) z_min = std::max(z_min, std::sqrt(1.0 - far_r2));
      double z_max = z_split;
      if (near_r2 < 1.0) z_max = std::min(z_max, std::sqrt(1.0 - near_r2));

      double best_bound = -1e9;
      int best_ax = -1;
      for (const auto &ax : zd_axes) {
        double z_term = (ax.lam >= 0) ? (ax.lam * z_min) : (ax.lam * z_max);
        double x_term = std::min(ax.vx * x1, ax.vx * x2);
        double y_term = std::min(ax.vy * y1, ax.vy * y2);
        double bound = z_term + x_term + y_term;
        if (bound > best_bound) {
          best_bound = bound;
          best_ax = ax.idx;
        }
      }
      std::cout << "Subbox (" << si << ", " << sj << "): best bound = " << best_bound << " (ax " << best_ax << ")\n";
    }
  }

  return 0;
}
