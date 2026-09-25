#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = vec3{ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
                 ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
                 ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  double norm_u0 = yocto::length(u0);
  vec3 u0_hat = yocto::normalize(u0);

  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::normalize(yocto::cross(u0, k1));

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  std::cout << "Cone half-angle alpha = " << alpha * 180.0 / M_PI << " deg\n";

  // Dense sampling of the 4 quadrants on S^2:
  // Each quadrant: z in [cos_alpha, 1], phi in quadrant interval
  int SAMPLES = 2000;
  std::vector<vec3> quad_pts[8];

  for (int q = 0; q < 8; q++) {
    double phi_min = q * M_PI / 4.0;
    double phi_max = (q + 1) * M_PI / 4.0;

    for (int i = 0; i < SAMPLES; i++) {
      double t = (double)i / (SAMPLES - 1);
      double z = cos_alpha + t * (1.0 - cos_alpha);
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      for (int j = 0; j < 50; j++) {
        double phi = phi_min + (double)j / 49.0 * (phi_max - phi_min);
        double x = r * std::cos(phi);
        double y = r * std::sin(phi);
        vec3 a = x * k1 + y * k2 + z * u0_hat;
        quad_pts[q].push_back(yocto::normalize(a));
      }
    }
  }

  // For each quadrant q, find the axis in all 5000 axes that maximizes the minimum dot product on quad_pts[q]
  int best_axis[8];
  double best_min_dot[8];

  for (int q = 0; q < 8; q++) {
    best_axis[q] = -1;
    best_min_dot[q] = -1e9;

    for (size_t i = 0; i < axes.size(); i++) {
      vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
      double min_d = 1e9;
      for (const auto &a : quad_pts[q]) {
        double d = yocto::dot(a, v);
        if (d < min_d) min_d = d;
      }
      if (min_d > best_min_dot[q]) {
        best_min_dot[q] = min_d;
        best_axis[q] = i;
      }
    }

    std::cout << "Octant " << q << ": best axis " << best_axis[q]
              << " has min_dot = " << std::fixed << std::setprecision(6) << best_min_dot[q] << "\n";
  }

  return 0;
}
