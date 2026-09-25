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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0_raw = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.017;
  double cos_cap = c_cone / norm_u0;
  double alpha_cap = std::acos(cos_cap);

  std::vector<std::pair<int, vec3>> good_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000200) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      good_axes.push_back({(int)i, v});
    }
  }

  // Sample points on the cap
  std::vector<vec3> cap_points;
  for (double r = 0; r <= alpha_cap; r += alpha_cap / 30.0) {
    int num_phi = std::max(1, (int)std::ceil(120.0 * (r / alpha_cap)));
    for (int p = 0; p < num_phi; p++) {
      double phi = 2.0 * M_PI * p / num_phi;
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      cap_points.push_back(pt);
    }
  }
  std::cout << "Cap points: " << cap_points.size() << "\n";

  // Greedy set cover with margin >= 0.0003
  double target_margin = 0.0003;
  std::vector<bool> covered(cap_points.size(), false);
  int uncovered_count = cap_points.size();

  std::vector<int> chosen_axes;
  while (uncovered_count > 0) {
    int best_ax = -1;
    int best_new_cov = 0;

    for (size_t i = 0; i < good_axes.size(); i++) {
      int new_cov = 0;
      for (size_t p = 0; p < cap_points.size(); p++) {
        if (!covered[p] && yocto::dot(cap_points[p], good_axes[i].second) >= target_margin) {
          new_cov++;
        }
      }
      if (new_cov > best_new_cov) {
        best_new_cov = new_cov;
        best_ax = i;
      }
    }

    if (best_new_cov == 0) {
      std::cout << "Cannot cover remaining " << uncovered_count << " points with margin " << target_margin << "!\n";
      break;
    }

    chosen_axes.push_back(good_axes[best_ax].first);
    for (size_t p = 0; p < cap_points.size(); p++) {
      if (!covered[p] && yocto::dot(cap_points[p], good_axes[best_ax].second) >= target_margin) {
        covered[p] = true;
        uncovered_count--;
      }
    }
    std::cout << "Added axis " << good_axes[best_ax].first << ", covered " << best_new_cov << ", remaining " << uncovered_count << "\n";
  }

  std::cout << "\nTotal chosen axes: " << chosen_axes.size() << "\n";
  for (int ax_id : chosen_axes) {
    std::cout << "Axis " << ax_id << ": delta = " << axes[ax_id].delta.ToDouble() << ", B = " << axes[ax_id].cert.B.ToDouble() << "\n";
  }

  return 0;
}
