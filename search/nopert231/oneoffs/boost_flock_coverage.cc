#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <unordered_set>
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

  double c_cone = 0.025;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  // Candidate axes: delta <= 0.000280
  std::vector<std::pair<int, vec3>> cand_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000280) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      cand_axes.push_back({(int)i, v});
    }
  }

  std::vector<int> chosen = {9030, 3449, 389, 36};
  std::unordered_set<int> chosen_set(chosen.begin(), chosen.end());
  std::vector<vec3> chosen_v;
  for (int idx : chosen) {
    double B = axes[idx].cert.B.ToDouble();
    chosen_v.push_back(vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B});
  }

  for (int step = 0; step < 10; step++) {
    // Find worst point on dense continuous grid
    double min_val = 1e9;
    vec3 worst_pt;
    for (double r = 0; r <= alpha; r += alpha / 200.0) {
      int num_phi = std::max(1, (int)std::ceil(400.0 * (r / alpha)));
      for (int p = 0; p < num_phi; p++) {
        double phi = 2.0 * M_PI * p / num_phi;
        vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
        double max_m = -1e9;
        for (const auto &v : chosen_v) max_m = std::max(max_m, yocto::dot(pt, v));
        if (max_m < min_val) {
          min_val = max_m;
          worst_pt = pt;
        }
      }
    }
    std::cout << "Step " << step << ": flock size " << chosen.size()
              << ", dense minimum coverage = " << min_val << "\n";

    if (min_val >= 0.0020) {
      std::cout << "SUCCESS! Minimum coverage >= 0.0020 achieved!\n";
      break;
    }

    // Find best candidate for worst_pt
    int best_cand = -1;
    double best_dot = -1e9;
    for (size_t i = 0; i < cand_axes.size(); i++) {
      if (chosen_set.count(cand_axes[i].first)) continue;
      double d = yocto::dot(worst_pt, cand_axes[i].second);
      if (d > best_dot) {
        best_dot = d;
        best_cand = i;
      }
    }

    if (best_cand < 0 || best_dot <= min_val) {
      std::cout << "No candidate can improve worst point! Best candidate had dot = " << best_dot << "\n";
      break;
    }

    chosen.push_back(cand_axes[best_cand].first);
    chosen_set.insert(cand_axes[best_cand].first);
    chosen_v.push_back(cand_axes[best_cand].second);
    std::cout << "  Added axis " << cand_axes[best_cand].first << " with dot = " << best_dot
              << " (delta " << axes[cand_axes[best_cand].first].delta.ToDouble() << ")\n";
  }

  std::cout << "\nFinal flock: ";
  for (int idx : chosen) std::cout << idx << " ";
  std::cout << "\n";

  return 0;
}
