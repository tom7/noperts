#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

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

  double c_cone = 0.017;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  std::cout << "norm_u0: " << norm_u0 << ", cos_alpha: " << cos_alpha << ", alpha_deg: " << alpha * 180.0 / M_PI << "\n";

  // Generate 5,000 cap points
  std::vector<vec3> cap_pts;
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);
  for (int i = 0; i < 5000; i++) {
    double t = (double)i / 4999.0;
    double r = alpha * std::sqrt(t);
    double phi = i * 2.399963229728653;
    vec3 pt = yocto::normalize(std::cos(r) * u0 + std::sin(r) * (std::cos(phi) * k1 + std::sin(phi) * k2));
    cap_pts.push_back(pt);
  }

  // Filter candidate flock axes: delta <= 0.000195
  std::vector<std::pair<int, vec3>> cand_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000195) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      // Must point somewhat towards u0
      if (yocto::dot(u0, v) > 0.0) {
        cand_axes.push_back({(int)i, v});
      }
    }
  }
  std::cout << "Candidate axes: " << cand_axes.size() << "\n";

  // Target c_core = 0.0020 (which satisfies c_core >= 0.00176)
  double target_c_core = 0.0020;
  std::vector<int> chosen;
  std::vector<bool> covered(cap_pts.size(), false);
  int covered_count = 0;

  while (covered_count < (int)cap_pts.size()) {
    int best_idx = -1;
    int best_new = -1;
    for (size_t i = 0; i < cand_axes.size(); i++) {
      int new_cov = 0;
      for (size_t p = 0; p < cap_pts.size(); p++) {
        if (!covered[p] && yocto::dot(cap_pts[p], cand_axes[i].second) >= target_c_core) {
          new_cov++;
        }
      }
      if (new_cov > best_new) {
        best_new = new_cov;
        best_idx = i;
      }
    }
    if (best_new <= 0) break;
    chosen.push_back(cand_axes[best_idx].first);
    for (size_t p = 0; p < cap_pts.size(); p++) {
      if (!covered[p] && yocto::dot(cap_pts[p], cand_axes[best_idx].second) >= target_c_core) {
        covered[p] = true;
        covered_count++;
      }
    }
    std::cout << "Added axis " << cand_axes[best_idx].first
              << ", newly covered: " << best_new
              << ", total covered: " << covered_count << " / " << cap_pts.size() << "\n";
  }

  std::cout << "Total flock axes chosen: " << chosen.size() << "\n";
  return 0;
}
