#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c0 = c_cone / norm_u0; // ~ 0.210027
  double R = std::sqrt(1.0 / (c0 * c0) - 1.0); // ~ 4.655
  double c_core = 0.0008;
  double target_gamma = c_core / c0; // ~ 0.003809

  std::cout << "R = " << R << ", target_gamma = " << target_gamma << "\n";

  struct LinearAxis {
    double A, B, C;
  };
  std::vector<LinearAxis> la;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                  axes[i].center.y.ToDouble(),
                                  axes[i].center.z.ToDouble()});
    la.push_back({yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Grid over [-R, R] x [-R, R]
  int N = 128;
  int total_cells_in_disk = 0;
  int covered_cells = 0;

  for (int ix = 0; ix < N; ix++) {
    double x0 = -R + 2.0 * R * ix / N;
    double x1 = -R + 2.0 * R * (ix + 1) / N;
    for (int iy = 0; iy < N; iy++) {
      double y0 = -R + 2.0 * R * iy / N;
      double y1 = -R + 2.0 * R * (iy + 1) / N;

      // Check if cell intersects disk of radius R
      // Distance from origin to cell
      double cx = (x0 > 0) ? x0 : ((x1 < 0) ? x1 : 0);
      double cy = (y0 > 0) ? y0 : ((y1 < 0) ? y1 : 0);
      if (cx * cx + cy * cy > R * R) continue;

      total_cells_in_disk++;

      // Check 4 vertices: (x0, y0), (x0, y1), (x1, y0), (x1, y1)
      bool ok = false;
      for (size_t i = 0; i < la.size(); i++) {
        double f00 = la[i].A + la[i].B * x0 + la[i].C * y0;
        double f01 = la[i].A + la[i].B * x0 + la[i].C * y1;
        double f10 = la[i].A + la[i].B * x1 + la[i].C * y0;
        double f11 = la[i].A + la[i].B * x1 + la[i].C * y1;
        if (f00 >= target_gamma && f01 >= target_gamma &&
            f10 >= target_gamma && f11 >= target_gamma) {
          ok = true;
          break;
        }
      }
      if (ok) covered_cells++;
    }
  }

  std::cout << "Grid " << N << "x" << N << ": " << covered_cells << " / " << total_cells_in_disk << " cells covered.\n";

  return 0;
}
