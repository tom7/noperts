#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

// We will test each axis by evaluating its exact Lean supportUpper!
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
  int N_ring = 16;
  double dphi = 2.0 * M_PI / N_ring;

  // Let's compute points for Sectors 12, 13, 14, 15
  std::vector<vec3> sector_points;
  for (int i = 12; i < 16; i++) {
    double phi1 = i * dphi;
    double phi2 = (i + 1) * dphi;
    vec3 p1 = yocto::normalize(std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi1) * k1 + std::sin(phi1) * k2));
    vec3 p2 = yocto::normalize(std::cos(alpha_cap) * u0 + std::sin(alpha_cap) * (std::cos(phi2) * k1 + std::sin(phi2) * k2));
    vec3 mid = yocto::normalize(p1 + p2);
    sector_points.push_back(p1);
    sector_points.push_back(p2);
    sector_points.push_back(mid);
  }

  // Which axes have delta <= 0.000165?
  std::cout << "Filtering axes...\n";
  struct Cand {
    int idx;
    double min_dot;
    double u0_dot;
    double delta;
  };
  std::vector<Cand> cands;

  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() > 0.000165) continue;
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    
    // Check dot with u0 and sector 14
    double u_dot = yocto::dot(u0, v);
    double min_d = 1e9;
    for (const auto &p : sector_points) {
      min_d = std::min(min_d, yocto::dot(p, v));
    }
    cands.push_back({(int)i, min_d, u_dot, axes[i].delta.ToDouble()});
  }

  std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
    return a.min_dot > b.min_dot;
  });

  std::cout << "Top 10 axes by min_dot on Sectors 12-15:\n";
  for (int i = 0; i < std::min(15, (int)cands.size()); i++) {
    std::cout << "Rank " << i << ": Axis " << cands[i].idx
              << ", min_dot = " << cands[i].min_dot
              << ", u0_dot = " << cands[i].u0_dot
              << ", delta = " << cands[i].delta << "\n";
  }

  return 0;
}
