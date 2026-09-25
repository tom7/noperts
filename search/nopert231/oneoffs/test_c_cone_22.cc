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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = {ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.z.ToDouble() / ann_cert.B.ToDouble()};

  double delta = 0.000234013;

  auto det4 = [](const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d) {
    auto d3 = [](const vec3 &x, const vec3 &y, const vec3 &z) {
      return yocto::dot(x, yocto::cross(y, z));
    };
    return -d3(b, c, d) + d3(a, c, d) - d3(a, b, d) + d3(a, b, c);
  };

  std::vector<vec3> p(axes.size());
  for (size_t i = 0; i < axes.size(); i++) {
    p[i] = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
            axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
            axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
  }

  for (double c_cone : {0.018, 0.020, 0.022, 0.024, 0.026}) {
    double best_c = 0;
    int best_t[3] = {-1, -1, -1};
    for (size_t i = 0; i < axes.size(); i++) {
      for (size_t j = i + 1; j < axes.size(); j++) {
        for (size_t k = j + 1; k < axes.size(); k++) {
          double c_val = 0.0005;
          double s = (c_val + delta) / c_cone;
          vec3 p0 = s * u0;
          double R = 1.75 * (c_val + delta);
          vec3 oct[6] = {
            {R, 0, 0}, {-R, 0, 0},
            {0, R, 0}, {0, -R, 0},
            {0, 0, R}, {0, 0, -R}
          };
          double D = det4(p0, p[i], p[j], p[k]);
          if (D <= 1e-9) continue;
          bool ok = true;
          for (int m = 0; m < 6; m++) {
            double l0 = det4(oct[m], p[i], p[j], p[k]) / D;
            double l1 = det4(p0, oct[m], p[j], p[k]) / D;
            double l2 = det4(p0, p[i], oct[m], p[k]) / D;
            double l3 = det4(p0, p[i], p[j], oct[m]) / D;
            if (l0 <= 1e-6 || l1 <= 1e-6 || l2 <= 1e-6 || l3 <= 1e-6) { ok = false; break; }
          }
          if (ok) {
            // Find max c for this triple
            double lo = c_val, hi = 0.010;
            for (int it = 0; it < 12; it++) {
              double mid = 0.5 * (lo + hi);
              double s_m = (mid + delta) / c_cone;
              vec3 p0_m = s_m * u0;
              double R_m = 1.75 * (mid + delta);
              vec3 oct_m[6] = {
                {R_m, 0, 0}, {-R_m, 0, 0},
                {0, R_m, 0}, {0, -R_m, 0},
                {0, 0, R_m}, {0, 0, -R_m}
              };
              double D_m = det4(p0_m, p[i], p[j], p[k]);
              bool ok_m = (D_m > 1e-9);
              if (ok_m) {
                for (int m = 0; m < 6; m++) {
                  double l0 = det4(oct_m[m], p[i], p[j], p[k]) / D_m;
                  double l1 = det4(p0_m, oct_m[m], p[j], p[k]) / D_m;
                  double l2 = det4(p0_m, p[i], oct_m[m], p[k]) / D_m;
                  double l3 = det4(p0_m, p[i], p[j], oct_m[m]) / D_m;
                  if (l0 <= 1e-6 || l1 <= 1e-6 || l2 <= 1e-6 || l3 <= 1e-6) { ok_m = false; break; }
                }
              }
              if (ok_m) lo = mid; else hi = mid;
            }
            if (lo > best_c) {
              best_c = lo;
              best_t[0] = i; best_t[1] = j; best_t[2] = k;
            }
          }
        }
      }
    }
    std::cout << "c_cone = " << c_cone << ": best c = " << best_c
              << " with (" << best_t[0] << ", " << best_t[1] << ", " << best_t[2] << ")\n";
  }
  return 0;
}
