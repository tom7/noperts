#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()}) / ax0.B.ToDouble();
  double cos_alpha = c_cone / norm_u0;

  // Audit all zero-defect axes
  struct Audited {
    int idx;
    vec3 v;
    AxisCertificate cert;
  };
  std::vector<Audited> audited;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      audited.push_back({(int)i, v, cert});
    }
  }

  // Generate 50,000 points on cap
  std::vector<vec3> cap_pts;
  for (double z = cos_alpha; z <= 1.0; z += 0.005) {
    double r_xy = std::sqrt(std::max(0.0, 1.0 - z * z));
    int N_phi = std::max(10, (int)(r_xy * 500));
    for (int p = 0; p < N_phi; p++) {
      double phi = 2.0 * M_PI * p / N_phi;
      cap_pts.push_back(z * u0 + r_xy * (std::cos(phi) * k1 + std::sin(phi) * k2));
    }
  }
  std::cout << "Generated " << cap_pts.size() << " cap points.\n";

  double target_margin = 0.005; // 5e-3 > delta = 1.6e-4
  std::vector<bool> covered(cap_pts.size(), false);
  size_t total_covered = 0;
  std::vector<int> chosen;

  while (total_covered < cap_pts.size()) {
    int best_ax = -1;
    size_t best_gain = 0;
    for (size_t a = 0; a < audited.size(); a++) {
      size_t gain = 0;
      for (size_t p = 0; p < cap_pts.size(); p++) {
        if (!covered[p] && yocto::dot(cap_pts[p], audited[a].v) >= target_margin) {
          gain++;
        }
      }
      if (gain > best_gain) {
        best_gain = gain;
        best_ax = a;
      }
    }
    if (best_gain == 0) break;
    chosen.push_back(best_ax);
    for (size_t p = 0; p < cap_pts.size(); p++) {
      if (!covered[p] && yocto::dot(cap_pts[p], audited[best_ax].v) >= target_margin) {
        covered[p] = true;
        total_covered++;
      }
    }
    std::cout << "Chosen axis " << audited[best_ax].idx << ", gain = " << best_gain
              << ", covered = " << total_covered << " / " << cap_pts.size() << "\n";
  }

  std::cout << "Total chosen flock axes: " << chosen.size() << "\n";
  return 0;
}
