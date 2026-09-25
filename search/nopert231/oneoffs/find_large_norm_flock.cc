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

  // Candidate axes: delta <= 0.000260 AND length(v) >= 0.05
  std::vector<std::pair<int, vec3>> cand_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000260) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      if (yocto::length(v) >= 0.05) {
        cand_axes.push_back({(int)i, v});
      }
    }
  }
  std::cout << "Candidate axes with length >= 0.05 and delta <= 0.000260: " << cand_axes.size() << "\n";

  // Generate 20,000 cap points
  std::vector<vec3> cap_pts;
  for (int i = 0; i < 20000; i++) {
    double t = (double)i / 19999.0;
    double r = alpha * std::sqrt(t);
    double phi = i * 2.399963229728653;
    vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
    cap_pts.push_back(pt);
  }

  // Greedy search
  std::vector<int> chosen;
  std::vector<vec3> chosen_v;
  std::unordered_set<int> chosen_set;

  for (int iter = 0; iter < 10; iter++) {
    double worst_cov = 1e9;
    int worst_p = -1;
    for (size_t p = 0; p < cap_pts.size(); p++) {
      double max_m = -1e9;
      for (const auto &v : chosen_v) max_m = std::max(max_m, yocto::dot(cap_pts[p], v));
      if (max_m < worst_cov) {
        worst_cov = max_m;
        worst_p = p;
      }
    }
    std::cout << "Iteration " << iter << ": flock size " << chosen.size() << ", worst coverage = " << worst_cov << "\n";
    if (worst_cov >= 0.0010) {
      std::cout << "Target coverage >= 0.0010 reached!\n";
      break;
    }

    int best_cand = -1;
    double best_dot = -1e9;
    for (size_t i = 0; i < cand_axes.size(); i++) {
      if (chosen_set.count(cand_axes[i].first)) continue;
      double d = (worst_p == -1) ? yocto::dot(u0, cand_axes[i].second) : yocto::dot(cap_pts[worst_p], cand_axes[i].second);
      if (d > best_dot) {
        best_dot = d;
        best_cand = i;
      }
    }
    if (best_cand < 0 || best_dot <= worst_cov) {
      std::cout << "Cannot improve! Best dot = " << best_dot << "\n";
      break;
    }
    chosen.push_back(cand_axes[best_cand].first);
    chosen_set.insert(cand_axes[best_cand].first);
    chosen_v.push_back(cand_axes[best_cand].second);
    std::cout << "  Added axis " << cand_axes[best_cand].first << " with dot = " << best_dot
              << ", norm = " << yocto::length(cand_axes[best_cand].second)
              << ", delta = " << axes[cand_axes[best_cand].first].delta.ToDouble() << "\n";
  }

  // Dense continuous check
  double min_val = 1e9;
  for (double r = 0; r <= alpha; r += alpha / 500.0) {
    int num_phi = std::max(1, (int)std::ceil(1000.0 * (r / alpha)));
    for (int p = 0; p < num_phi; p++) {
      double phi = 2.0 * M_PI * p / num_phi;
      vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
      double max_m = -1e9;
      for (const auto &v : chosen_v) max_m = std::max(max_m, yocto::dot(pt, v));
      min_val = std::min(min_val, max_m);
    }
  }
  std::cout << "CONTINUOUS GRID MINIMUM COVERAGE: " << min_val << "\n";

  return 0;
}
