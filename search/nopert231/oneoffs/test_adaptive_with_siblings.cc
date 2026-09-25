#include <iostream>
#include <vector>
#include <cmath>
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
  double c_core = 0.000234013;
  double cos_cap = c_cone / norm_u0;
  double alpha_cap = std::acos(cos_cap);

  std::vector<std::pair<vec3, int>> candidate_v;

  // 1. Add all hull support axes with delta <= 0.000235
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000235) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      candidate_v.push_back({v, (int)i});
    }
  }

  // 2. Add sibling axes with edge 13 varied mixes
  std::vector<AxisCertificate> sibling_certs;
  for (int mix = 0; mix <= 1000; mix += 100) {
    ContactInfo c[3] = {
      {3, 2, 2, 1, 800, 2},
      {1, 4, 4, 8, 800, 4},
      {13, 14, 14, 15, mix, 14}
    };
    AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
    if (Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(1, 1000))) {
      if (del.ToDouble() <= 0.000235) {
        double B = ax.B.ToDouble();
        vec3 v = vec3{ctr.x.ToDouble() / B, ctr.y.ToDouble() / B, ctr.z.ToDouble() / B};
        int sib_id = 100000 + mix;
        candidate_v.push_back({v, sib_id});
      }
    }
  }

  std::cout << "Total candidate axes: " << candidate_v.size() << "\n";

  auto try_cover = [&](const vec3 &p1, const vec3 &p2, const vec3 &p3) -> int {
    for (const auto &cv : candidate_v) {
      double m1 = yocto::dot(p1, cv.first) - c_core;
      if (m1 < 0) continue;
      double m2 = yocto::dot(p2, cv.first) - c_core;
      if (m2 < 0) continue;
      double m3 = yocto::dot(p3, cv.first) - c_core;
      if (m3 < 0) continue;
      return cv.second;
    }
    return -1;
  };

  int leaf_count = 0;
  std::vector<int> used_axes;

  auto subdivide_adaptive = [&](auto &self, const vec3 &p1, const vec3 &p2, const vec3 &p3, int depth) -> bool {
    int ax = try_cover(p1, p2, p3);
    if (ax >= 0) {
      leaf_count++;
      used_axes.push_back(ax);
      return true;
    }
    if (depth >= 7) {
      return false;
    }
    vec3 m12 = yocto::normalize(p1 + p2);
    vec3 m23 = yocto::normalize(p2 + p3);
    vec3 m31 = yocto::normalize(p3 + p1);
    return self(self, p1, m12, m31, depth + 1) &&
           self(self, m12, p2, m23, depth + 1) &&
           self(self, m31, m23, p3, depth + 1) &&
           self(self, m12, m23, m31, depth + 1);
  };

  int N_ring = 16;
  double dphi = 2.0 * M_PI / N_ring;
  bool all_covered = true;

  for (int i = 0; i < N_ring; i++) {
    double phi1 = i * dphi;
    double phi2 = (i + 1) * dphi;
    vec3 p1 = std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi1) * k1 + std::sin(phi1) * k2);
    vec3 p2 = std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi2) * k1 + std::sin(phi2) * k2);
    p1 = yocto::normalize(p1);
    p2 = yocto::normalize(p2);

    bool res = subdivide_adaptive(subdivide_adaptive, u0, p1, p2, 0);
    if (!res) {
      std::cout << "Failed on base sector " << i << "\n";
      all_covered = false;
    } else {
      std::cout << "Sector " << i << " covered!\n";
    }
  }

  std::cout << "Adaptive subdivision result: all_covered = " << all_covered << "\n";
  std::cout << "Total leaves: " << leaf_count << "\n";
  std::sort(used_axes.begin(), used_axes.end());
  used_axes.erase(std::unique(used_axes.begin(), used_axes.end()), used_axes.end());
  std::cout << "Distinct core axes used: " << used_axes.size() << "\n";
  for (int ax : used_axes) {
    std::cout << "  Axis " << ax << "\n";
  }

  return 0;
}
