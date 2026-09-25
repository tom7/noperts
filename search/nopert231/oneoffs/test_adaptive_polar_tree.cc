#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

double MinCos(double ph0, double ph1, double psi) {
  double a0 = ph0 - psi;
  double a1 = ph1 - psi;
  if (a1 - a0 >= 2 * M_PI) return -1.0;
  double k0 = std::ceil((a0 - M_PI) / (2 * M_PI));
  double k1 = std::floor((a1 - M_PI) / (2 * M_PI));
  if (k0 <= k1) return -1.0;
  return std::min(std::cos(a0), std::cos(a1));
}

double MinTrigCombo(double th0, double th1, double lam, double C) {
  double min_val = std::min(lam * std::cos(th0) + C * std::sin(th0),
                            lam * std::cos(th1) + C * std::sin(th1));
  double th_crit = std::atan2(C, lam);
  double th_crit_min = th_crit + M_PI;
  while (th_crit_min > th1) th_crit_min -= 2 * M_PI;
  while (th_crit_min < th0) th_crit_min += 2 * M_PI;
  if (th_crit_min >= th0 && th_crit_min <= th1) {
    min_val = std::min(min_val, lam * std::cos(th_crit_min) + C * std::sin(th_crit_min));
  }
  return min_val;
}

struct PolarCell {
  double th0, th1;
  double ph0, ph1;
  int depth;
};

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
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);

  double c_core = 0.0008;

  struct AxisData {
    double lam, mu, psi;
  };
  std::vector<AxisData> ad;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                  axes[i].center.y.ToDouble(),
                                  axes[i].center.z.ToDouble()});
    double lam = yocto::dot(u0, v);
    double d1 = yocto::dot(e1, v);
    double d2 = yocto::dot(e2, v);
    ad.push_back({lam, std::sqrt(d1 * d1 + d2 * d2), std::atan2(d2, d1)});
  }

  // Root cells: 4 rings x 8 sectors = 32 initial cells
  std::vector<PolarCell> queue;
  for (int it = 0; it < 4; it++) {
    double th0 = (double)it / 4 * alpha;
    double th1 = (double)(it + 1) / 4 * alpha;
    for (int ip = 0; ip < 8; ip++) {
      double ph0 = 2.0 * M_PI * ip / 8;
      double ph1 = 2.0 * M_PI * (ip + 1) / 8;
      queue.push_back({th0, th1, ph0, ph1, 0});
    }
  }

  int closed_leaves = 0;
  int max_depth = 12;
  std::vector<PolarCell> pending;

  while (!queue.empty()) {
    PolarCell cell = queue.back();
    queue.pop_back();

    bool ok = false;
    for (size_t i = 0; i < ad.size(); i++) {
      double mc = MinCos(cell.ph0, cell.ph1, ad[i].psi);
      double mv = MinTrigCombo(cell.th0, cell.th1, ad[i].lam, ad[i].mu * mc);
      if (mv >= c_core) {
        ok = true;
        break;
      }
    }

    if (ok) {
      closed_leaves++;
    } else if (cell.depth < max_depth) {
      double mth = 0.5 * (cell.th0 + cell.th1);
      double mph = 0.5 * (cell.ph0 + cell.ph1);
      queue.push_back({cell.th0, mth, cell.ph0, mph, cell.depth + 1});
      queue.push_back({mth, cell.th1, cell.ph0, mph, cell.depth + 1});
      queue.push_back({cell.th0, mth, mph, cell.ph1, cell.depth + 1});
      queue.push_back({mth, cell.th1, mph, cell.ph1, cell.depth + 1});
    } else {
      pending.push_back(cell);
    }
  }

  std::cout << "Adaptive Polar Tree Result:\n";
  std::cout << "  Closed leaves: " << closed_leaves << "\n";
  std::cout << "  Pending leaves at max_depth " << max_depth << ": " << pending.size() << "\n";

  return 0;
}
