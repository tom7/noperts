#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Box2D {
  double x_min, x_max, y_min, y_max;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = {ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  double norm_u0 = yocto::length(u0);
  vec3 dir_u0 = yocto::normalize(u0);

  // Basis k1, k2 perp to u0:
  vec3 k1 = yocto::normalize(yocto::cross(dir_u0, std::abs(dir_u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(dir_u0, k1);

  double c_cone = 0.015;
  double c_core = 0.005; // target margin 0.005

  std::cout << "norm_u0 = " << norm_u0 << "\n";
  std::cout << "k1 = (" << k1.x << ", " << k1.y << ", " << k1.z << ")\n";
  std::cout << "k2 = (" << k2.x << ", " << k2.y << ", " << k2.z << ")\n";

  // Precompute decomposition of each zero-defect axis:
  // v = c1 k1 + c2 k2 + c0 u0
  // Note: v . k1 = c1, v . k2 = c2, v . dir_u0 = c0 * norm_u0  =>  c0 = (v . dir_u0) / norm_u0
  struct Decomp {
    size_t axis_idx;
    double c1, c2, c0;
    vec3 v;
  };
  std::vector<Decomp> decomps;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double c1 = yocto::dot(v, k1);
    double c2 = yocto::dot(v, k2);
    double c0 = yocto::dot(v, dir_u0) / norm_u0;
    decomps.push_back({i, c1, c2, c0, v});
  }
  std::cout << "Total axes evaluated: " << decomps.size() << "\n";

  // Test grid sizes N x N on [-1, 1] x [-1, 1]:
  for (int N : {2, 3, 4, 5, 6, 8, 10, 12, 16}) {
    double step = 2.0 / N;
    int covered_boxes = 0;
    int total_boxes = 0;
    std::vector<int> box_axis(N * N, -1);
    for (int ix = 0; ix < N; ix++) {
      double x_min = -1.0 + ix * step;
      double x_max = x_min + step;
      for (int iy = 0; iy < N; iy++) {
        double y_min = -1.0 + iy * step;
        double y_max = y_min + step;

        // Check if this box intersects the disk x^2 + y^2 <= 1:
        double closest_x = std::clamp(0.0, x_min, x_max);
        double closest_y = std::clamp(0.0, y_min, y_max);
        if (closest_x * closest_x + closest_y * closest_y > 1.0) {
          // outside disk, skip!
          continue;
        }
        total_boxes++;

        for (const auto &d : decomps) {
          double c0_term = (d.c0 >= 0 ? d.c0 * c_cone : d.c0 * norm_u0);
          double corner_val = (d.c1 >= 0 ? d.c1 * x_min : d.c1 * x_max) +
                              (d.c2 >= 0 ? d.c2 * y_min : d.c2 * y_max) +
                              c0_term;
          if (corner_val >= c_core) {
            covered_boxes++;
            box_axis[ix * N + iy] = d.axis_idx;
            break;
          }
        }
      }
    }
    std::cout << "N = " << N << " (" << step << " step): covered " << covered_boxes << " / " << total_boxes << " boxes\n";
  }

  return 0;
}
