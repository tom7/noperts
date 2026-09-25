#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct AxisData {
  vec3 v;
  double c0, c1, c2;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<AxisData> candidate_axes;

  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double d0 = yocto::dot(P0, v);
      double d1 = yocto::dot(E1, v);
      double d2 = yocto::dot(E2, v);
      candidate_axes.push_back({v, d0, d1, d2});
    }
  }

  // Add grid mixes
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate ax_cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &ax_cert, &center, &delta, &err, BigRat(0))) {
        if (delta.ToDouble() <= box_delta) {
          double B = ax_cert.B.ToDouble();
          vec3 v = vec3{center.x.ToDouble() / B, center.y.ToDouble() / B, center.z.ToDouble() / B};
          double d0 = yocto::dot(P0, v);
          double d1 = yocto::dot(E1, v);
          double d2 = yocto::dot(E2, v);
          candidate_axes.push_back({v, d0, d1, d2});
        }
      }
    }
  }

  int N = 16;
  for (int i = 0; i < N; i++) {
    double x_min = -R + 2.0 * R * i / N;
    double x_max = -R + 2.0 * R * (i + 1) / N;
    for (int j = 0; j < N; j++) {
      double y_min = -R + 2.0 * R * j / N;
      double y_max = -R + 2.0 * R * (j + 1) / N;

      double cx = std::max(0.0, std::max(x_min, -x_max));
      double cy = std::max(0.0, std::max(y_min, -y_max));
      if (cx * cx + cy * cy > R_sq) continue;

      bool box_covered = false;
      double best_min_corner = -1e9;
      for (size_t a = 0; a < candidate_axes.size(); a++) {
        const auto &ax = candidate_axes[a];
        double c1_corner = (ax.c1 >= 0) ? (ax.c1 * x_min) : (ax.c1 * x_max);
        double c2_corner = (ax.c2 >= 0) ? (ax.c2 * y_min) : (ax.c2 * y_max);
        double min_corner = c1_corner + c2_corner + ax.c0 * c_cone;
        best_min_corner = std::max(best_min_corner, min_corner);
        if (min_corner >= c_core) {
          box_covered = true;
          break;
        }
      }
      if (!box_covered) {
        std::cout << "Uncovered box: [" << x_min << ", " << x_max << "] x ["
                  << y_min << ", " << y_max << "], center = (" << 0.5*(x_min+x_max) << ", " << 0.5*(y_min+y_max) << ")\n"
                  << "  best min corner = " << best_min_corner << ", deficit = " << c_core - best_min_corner << "\n";
        vec3 p_center = P0 + 0.5*(x_min+x_max) * E1 + 0.5*(y_min+y_max) * E2;
        vec3 a_dir = yocto::normalize(p_center);
        std::cout << "  adversary unit vector at center: (" << a_dir.x << ", " << a_dir.y << ", " << a_dir.z << ")\n";
        std::cout << "  dot with u0 = " << yocto::dot(a_dir, u0) << "\n";
      }
    }
  }

  return 0;
}
