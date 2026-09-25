#include <iostream>
#include <vector>
#include <cmath>
#include <numbers>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

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
  double c_core = 0.00055; // our target c_core
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);

  std::cout << "Target disk radius R = " << R << "\n";

  // Filter valid zero-defect axes
  double box_delta = 234013.0 / 1000000000.0;
  std::vector<vec3> valid_v;
  std::vector<int> valid_orig_idx;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= box_delta) {
      vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                    axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
      valid_v.push_back(v);
      valid_orig_idx.push_back((int)i);
    }
  }
  std::cout << "Valid axes count: " << valid_v.size() << "\n";

  auto check_pt = [&](double X, double Y, int a) {
    vec3 p = P0 + X * E1 + Y * E2;
    return yocto::dot(p, valid_v[a]) >= c_core * yocto::length(p);
  };

  // Test regular N-gons circumscribing the circle of radius R
  for (int N : {8, 10, 12, 16, 20, 24, 32}) {
    double alpha = std::numbers::pi / N;
    double R_poly = R / std::cos(alpha);

    // Vertices of N-gon
    std::vector<std::pair<double, double>> poly;
    for (int k = 0; k < N; k++) {
      double theta = 2.0 * std::numbers::pi * k / N;
      poly.push_back({R_poly * std::cos(theta), R_poly * std::sin(theta)});
    }

    // Each triangle is (0, poly[k], poly[(k+1)%N])
    bool all_covered = true;
    std::vector<int> tri_axis(N, -1);
    for (int k = 0; k < N; k++) {
      double x1 = 0, y1 = 0;
      double x2 = poly[k].first, y2 = poly[k].second;
      double x3 = poly[(k+1)%N].first, y3 = poly[(k+1)%N].second;

      int best_a = -1;
      for (size_t a = 0; a < valid_v.size(); a++) {
        if (check_pt(x1, y1, a) && check_pt(x2, y2, a) && check_pt(x3, y3, a)) {
          best_a = a;
          break;
        }
      }
      if (best_a == -1) {
        all_covered = false;
        break;
      }
      tri_axis[k] = best_a;
    }

    std::cout << "N = " << N << " (R_poly = " << R_poly << "): all_covered = " << all_covered;
    if (all_covered) {
      std::set<int> distinct(tri_axis.begin(), tri_axis.end());
      std::cout << " with " << distinct.size() << " distinct axes!";
    }
    std::cout << "\n";
  }

  return 0;
}
