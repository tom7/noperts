#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct PolarSector {
  double th0, th1;
  double ph0, ph1;
};

// Returns min_{ph in [ph0, ph1]} cos(ph - psi)
double MinCos(double ph0, double ph1, double psi) {
  // Normalize angles mod 2pi
  auto norm = [](double a) {
    while (a < 0) a += 2 * M_PI;
    while (a >= 2 * M_PI) a -= 2 * M_PI;
    return a;
  };
  // Shift so psi = 0
  double a0 = ph0 - psi;
  double a1 = ph1 - psi;
  // If the interval length >= 2pi, it contains pi (cos = -1)
  if (a1 - a0 >= 2 * M_PI) return -1.0;
  // Check if angle pi (mod 2pi) is in [a0, a1]
  double k0 = std::ceil((a0 - M_PI) / (2 * M_PI));
  double k1 = std::floor((a1 - M_PI) / (2 * M_PI));
  if (k0 <= k1) return -1.0;
  // Otherwise min is at one of the endpoints
  return std::min(std::cos(a0), std::cos(a1));
}

// Returns min_{th in [th0, th1]} (lam * cos(th) + C * sin(th))
double MinTrigCombo(double th0, double th1, double lam, double C) {
  // f(th) = lam * cos(th) + C * sin(th) = R * cos(th - gamma)
  // Check critical points f'(th) = -lam * sin(th) + C * cos(th) = 0 => tan(th) = C / lam
  double min_val = std::min(lam * std::cos(th0) + C * std::sin(th0),
                            lam * std::cos(th1) + C * std::sin(th1));
  double th_crit = std::atan2(C, lam); // max of f
  double th_crit_min = th_crit + M_PI; // min of f
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

  // Flock axes
  int flock_indices[4] = {3054, 31, 3059, 3058};
  struct FlockParam {
    double lam;
    double mu;
    double psi;
  };
  FlockParam fp[4];
  for (int k = 0; k < 4; k++) {
    vec3 v = yocto::normalize(vec3{axes[flock_indices[k]].center.x.ToDouble(),
                                  axes[flock_indices[k]].center.y.ToDouble(),
                                  axes[flock_indices[k]].center.z.ToDouble()});
    fp[k].lam = yocto::dot(u0, v);
    double d1 = yocto::dot(e1, v);
    double d2 = yocto::dot(e2, v);
    fp[k].mu = std::sqrt(d1 * d1 + d2 * d2);
    fp[k].psi = std::atan2(d2, d1);
    std::cout << "Flock axis " << k << " (idx " << flock_indices[k] << "): "
              << "lam = " << fp[k].lam << ", mu = " << fp[k].mu << ", psi = " << fp[k].psi * 180 / M_PI << " deg\n";
  }

  double c_core = 0.005;

  // Let's test a simple grid of sectors over [0, alpha] x [0, 2pi]
  for (int N_th = 4; N_th <= 32; N_th *= 2) {
    for (int N_ph = 8; N_ph <= 64; N_ph *= 2) {
      int total_sectors = N_th * N_ph;
      int closed_sectors = 0;
      for (int it = 0; it < N_th; it++) {
        double th0 = (double)it / N_th * alpha;
        double th1 = (double)(it + 1) / N_th * alpha;
        for (int ip = 0; ip < N_ph; ip++) {
          double ph0 = 2.0 * M_PI * ip / N_ph;
          double ph1 = 2.0 * M_PI * (ip + 1) / N_ph;

          bool covered = false;
          for (int k = 0; k < 4; k++) {
            double min_cos = MinCos(ph0, ph1, fp[k].psi);
            // In [th0, th1], sin(th) >= 0. So C = mu * min_cos gives lower bound on lateral part
            double min_val = MinTrigCombo(th0, th1, fp[k].lam, fp[k].mu * min_cos);
            if (min_val >= c_core) {
              covered = true;
              break;
            }
          }
          if (covered) closed_sectors++;
        }
      }
      std::cout << "Grid " << N_th << " x " << N_ph << " (" << total_sectors << " sectors): "
                << closed_sectors << " / " << total_sectors << " covered.\n";
      if (closed_sectors == total_sectors) {
        std::cout << "SUCCESS! 100% COVERAGE PROVED with " << total_sectors << " sectors!\n";
        return 0;
      }
    }
  }

  return 0;
}
