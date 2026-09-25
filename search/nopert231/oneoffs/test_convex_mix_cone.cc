#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double c0 = c_cone / norm_u0; // ~ 0.210027
  double R = std::sqrt(1.0 / (c0 * c0) - 1.0); // ~ 4.655

  std::cout << "R = " << R << "\n";

  // We want to find mu in Delta_K to maximize: A_mu - R * sqrt(B_mu^2 + C_mu^2)
  // where A_mu = dot(u0, v_mu), B_mu = dot(e1, v_mu), C_mu = dot(e2, v_mu)
  // Let's test random convex combinations or top axes
  struct AxisData {
    double A, B, C;
  };
  std::vector<AxisData> ad;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                  axes[i].center.y.ToDouble(),
                                  axes[i].center.z.ToDouble()});
    ad.push_back({yocto::dot(u0, v), yocto::dot(e1, v), yocto::dot(e2, v)});
  }

  // Best single axis:
  double best_single = -1e9;
  int best_single_idx = -1;
  for (size_t i = 0; i < ad.size(); i++) {
    double val = ad[i].A - R * std::sqrt(ad[i].B * ad[i].B + ad[i].C * ad[i].C);
    if (val > best_single) {
      best_single = val;
      best_single_idx = i;
    }
  }
  std::cout << "Best single axis [" << best_single_idx << "]: margin = " << best_single << "\n";

  // Let's optimize a mix of axes using Frank-Wolfe / gradient descent
  std::vector<double> mu(ad.size(), 0.0);
  mu[best_single_idx] = 1.0;
  double cur_A = ad[best_single_idx].A;
  double cur_B = ad[best_single_idx].B;
  double cur_C = ad[best_single_idx].C;

  for (int iter = 0; iter < 10000; iter++) {
    double norm_perp = std::sqrt(cur_B * cur_B + cur_C * cur_C);
    // Gradient of A - R * sqrt(B^2 + C^2) with respect to (A, B, C):
    // grad_A = 1
    // grad_B = -R * cur_B / norm_perp
    // grad_C = -R * cur_C / norm_perp
    double gA = 1.0;
    double gB = (norm_perp > 1e-12) ? (-R * cur_B / norm_perp) : 0.0;
    double gC = (norm_perp > 1e-12) ? (-R * cur_C / norm_perp) : 0.0;

    // Find axis k that maximizes dot(grad, (A_k, B_k, C_k))
    int best_k = -1;
    double best_dot = -1e9;
    for (size_t i = 0; i < ad.size(); i++) {
      double d = gA * ad[i].A + gB * ad[i].B + gC * ad[i].C;
      if (d > best_dot) {
        best_dot = d;
        best_k = i;
      }
    }

    // Step size gamma = 2 / (iter + 2)
    double step = 2.0 / (iter + 2.0);
    cur_A = (1.0 - step) * cur_A + step * ad[best_k].A;
    cur_B = (1.0 - step) * cur_B + step * ad[best_k].B;
    cur_C = (1.0 - step) * cur_C + step * ad[best_k].C;
  }

  double final_val = cur_A - R * std::sqrt(cur_B * cur_B + cur_C * cur_C);
  std::cout << "Optimized convex mix: A = " << cur_A << ", perp = " << std::sqrt(cur_B * cur_B + cur_C * cur_C)
            << ", val = " << final_val << "\n";

  return 0;
}
