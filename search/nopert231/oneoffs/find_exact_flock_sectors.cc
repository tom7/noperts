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

  struct FlockParam {
    int index;
    double lam;
    double mu;
    double psi;
  };
  std::vector<FlockParam> all_fp;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(),
                                  axes[i].center.y.ToDouble(),
                                  axes[i].center.z.ToDouble()});
    double lam = yocto::dot(u0, v);
    double d1 = yocto::dot(e1, v);
    double d2 = yocto::dot(e2, v);
    all_fp.push_back({(int)i, lam, std::sqrt(d1 * d1 + d2 * d2), std::atan2(d2, d1)});
  }

  int N_th = 8;
  int N_ph = 32;
  int total_sectors = N_th * N_ph;
  double c_core = 0.005;

  struct Sector {
    double th0, th1, ph0, ph1;
  };
  std::vector<Sector> sectors;
  for (int it = 0; it < N_th; it++) {
    double th0 = (double)it / N_th * alpha;
    double th1 = (double)(it + 1) / N_th * alpha;
    for (int ip = 0; ip < N_ph; ip++) {
      double ph0 = 2.0 * M_PI * ip / N_ph;
      double ph1 = 2.0 * M_PI * (ip + 1) / N_ph;
      sectors.push_back({th0, th1, ph0, ph1});
    }
  }

  // Precompute coverage matrix: cov[axis][sector] = (min_val >= c_core)
  std::vector<std::vector<bool>> cov(all_fp.size(), std::vector<bool>(total_sectors, false));
  for (size_t i = 0; i < all_fp.size(); i++) {
    for (int s = 0; s < total_sectors; s++) {
      double min_cos = MinCos(sectors[s].ph0, sectors[s].ph1, all_fp[i].psi);
      double min_val = MinTrigCombo(sectors[s].th0, sectors[s].th1, all_fp[i].lam, all_fp[i].mu * min_cos);
      if (min_val >= c_core) {
        cov[i][s] = true;
      }
    }
  }

  // Greedy set cover
  std::vector<bool> covered(total_sectors, false);
  int num_covered = 0;
  std::vector<int> chosen_axes;

  while (num_covered < total_sectors) {
    int best_axis = -1;
    int best_gain = 0;
    for (size_t i = 0; i < all_fp.size(); i++) {
      int gain = 0;
      for (int s = 0; s < total_sectors; s++) {
        if (!covered[s] && cov[i][s]) gain++;
      }
      if (gain > best_gain) {
        best_gain = gain;
        best_axis = i;
      }
    }
    if (best_axis == -1 || best_gain == 0) {
      std::cout << "Cannot cover remaining " << total_sectors - num_covered << " sectors!\n";
      break;
    }
    chosen_axes.push_back(best_axis);
    for (int s = 0; s < total_sectors; s++) {
      if (!covered[s] && cov[best_axis][s]) {
        covered[s] = true;
        num_covered++;
      }
    }
    std::cout << "Added axis " << best_axis << " (gain " << best_gain << "), total covered: "
              << num_covered << " / " << total_sectors << "\n";
  }

  if (num_covered == total_sectors) {
    std::cout << "SUCCESS! Flock of " << chosen_axes.size() << " axes achieves 100.0% coverage of all "
              << total_sectors << " sectors!\n";
    std::cout << "Chosen axis indices: ";
    for (int a : chosen_axes) std::cout << a << " ";
    std::cout << "\n";
  }

  return 0;
}
