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

  // We tested c_cone = 25/1000 earlier and it passed Lean decide!
  // What if c_cone = 0.020? Then alpha = arccos(0.020 / 0.0511) = 66.9 deg
  // Or c_cone = 0.024? Then alpha = arccos(0.024 / 0.0511) = 62.0 deg
  // Or with c_cone = 0.017, alpha = 70.5 deg.
  for (double c_cone : {0.017, 0.020, 0.024}) {
    double cos_alpha = c_cone / norm_u0;
    double alpha = std::acos(cos_alpha);
    std::cout << "\nTesting c_cone = " << c_cone << ", alpha = " << alpha * 180.0 / M_PI << " deg:\n";

    // Sample 2,000 cap points
    std::vector<vec3> cap_pts;
    vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
    vec3 k2 = yocto::cross(u0, k1);
    for (int i = 0; i < 2000; i++) {
      double t = (double)i / 1999.0;
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
        if (yocto::dot(u0, v) > 0.0) {
          cand_axes.push_back({(int)i, v});
        }
      }
    }

    // Try target_c_core = 0.0018, 0.0015, 0.0010
    for (double target_c : {0.0020, 0.0018, 0.0015}) {
      std::vector<int> chosen;
      std::vector<bool> covered(cap_pts.size(), false);
      int covered_count = 0;

      while (covered_count < (int)cap_pts.size()) {
        int best_idx = -1;
        int best_new = -1;
        for (size_t i = 0; i < cand_axes.size(); i++) {
          int new_cov = 0;
          for (size_t p = 0; p < cap_pts.size(); p++) {
            if (!covered[p] && yocto::dot(cap_pts[p], cand_axes[i].second) >= target_c) {
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
          if (!covered[p] && yocto::dot(cap_pts[p], cand_axes[best_idx].second) >= target_c) {
            covered[p] = true;
            covered_count++;
          }
        }
      }
      std::cout << "  target_c = " << target_c << ": covered " << covered_count << " / " << cap_pts.size()
                << " with " << chosen.size() << " axes\n";
    }
  }
  return 0;
}
