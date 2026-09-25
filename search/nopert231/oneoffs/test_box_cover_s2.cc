#include <iostream>
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
  double norm_u0 = yocto::length(u0);
  vec3 u0_hat = u0 / norm_u0;

  vec3 arbitrary = (std::abs(u0_hat.z) < 0.9) ? vec3{0, 0, 1} : vec3{1, 0, 0};
  vec3 k1 = yocto::normalize(yocto::cross(u0_hat, arbitrary));
  vec3 k2 = yocto::cross(u0_hat, k1);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  auto hull_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  for (const auto &ax : hull_axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
  for (int m1 = 0; m1 <= 1000; m1 += 25) {
    for (int m2 = 0; m2 <= 1000; m2 += 25) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  double c_cone = 0.015;
  double c_core = 0.000234013;

  struct Coeffs {
    int ax_idx;
    double c1, c2, c0;
  };
  std::vector<Coeffs> all_coeffs;
  for (size_t i = 0; i < valid_axes.size(); i++) {
    double B = valid_axes[i].cert.B.ToDouble();
    vec3 v = vec3{valid_axes[i].center.x.ToDouble() / B,
                  valid_axes[i].center.y.ToDouble() / B,
                  valid_axes[i].center.z.ToDouble() / B};
    double c0 = yocto::dot(v, u0) / (norm_u0 * norm_u0);
    double c1 = yocto::dot(v, k1);
    double c2 = yocto::dot(v, k2);
    all_coeffs.push_back({(int)i, c1, c2, c0});
  }
  std::cout << "Total valid axes: " << all_coeffs.size() << "\n";

  auto worst_corner = [&](const Coeffs &cf, double xmin, double xmax, double ymin, double ymax) {
    double v1 = (cf.c1 >= 0) ? cf.c1 * xmin : cf.c1 * xmax;
    double v2 = (cf.c2 >= 0) ? cf.c2 * ymin : cf.c2 * ymax;
    double u_term = (cf.c0 >= 0) ? cf.c0 * c_cone : cf.c0 * norm_u0;
    return v1 + v2 + u_term;
  };

  auto box_dist_sq = [](double xmin, double xmax, double ymin, double ymax) {
    double dx = (0.0 < xmin) ? xmin : ((0.0 > xmax) ? xmax : 0.0);
    double dy = (0.0 < ymin) ? ymin : ((0.0 > ymax) ? ymax : 0.0);
    return dx * dx + dy * dy;
  };

  for (int N : {2, 4, 8, 16, 32, 64}) {
    int uncovered = 0;
    int disk_boxes = 0;
    for (int i = 0; i < N; i++) {
      double xmin = -1.0 + 2.0 * i / N;
      double xmax = -1.0 + 2.0 * (i + 1) / N;
      for (int j = 0; j < N; j++) {
        double ymin = -1.0 + 2.0 * j / N;
        double ymax = -1.0 + 2.0 * (j + 1) / N;
        if (box_dist_sq(xmin, xmax, ymin, ymax) > 1.0) continue;
        disk_boxes++;
        bool covered = false;
        for (const auto &cf : all_coeffs) {
          if (worst_corner(cf, xmin, xmax, ymin, ymax) >= c_core) {
            covered = true;
            break;
          }
        }
        if (!covered) uncovered++;
      }
    }
    std::cout << "Grid " << N << "x" << N << " (disk boxes: " << disk_boxes << "): uncovered = " << uncovered << "\n";
  }

  return 0;
}
