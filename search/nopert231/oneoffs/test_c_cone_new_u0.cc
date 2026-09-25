#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static double Det3(vec3 a, vec3 b, vec3 c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo new_c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {8, 9, 9, 10, 0, 9}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, new_c0, &ax0, &ctr0, &del0, &err, BigRat(0));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double delta = del0.ToDouble();

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  std::vector<vec3> p;
  std::vector<int> orig_idx;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      p.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                   ctr.y.ToDouble() / cert.B.ToDouble(),
                   ctr.z.ToDouble() / cert.B.ToDouble()});
      orig_idx.push_back(i);
    }
  }

  vec3 oct[6] = {
    vec3(1, 0, 0), vec3(-1, 0, 0),
    vec3(0, 1, 0), vec3(0, -1, 0),
    vec3(0, 0, 1), vec3(0, 0, -1)
  };

  for (double c_cone = 0.005; c_cone <= 0.012; c_cone += 0.001) {
    double best_c = 0.0;
    int best_triple[3] = {-1, -1, -1};

    for (size_t i = 0; i < p.size(); i++) {
      for (size_t j = i + 1; j < p.size(); j++) {
        for (size_t k = j + 1; k < p.size(); k++) {
          // Let us test c_val = 0.0005
          double c_val = 0.0005;
          double s = (c_val + delta) / c_cone;
          vec3 p0 = s * u0;
          double R = 1.75 * (c_val + delta);

          vec3 a = p0 - p[k], b = p[i] - p[k], d = p[j] - p[k];
          double det = Det3(a, b, d);
          if (std::abs(det) < 1e-12) continue;

          bool ok = true;
          for (int v = 0; v < 6; v++) {
            vec3 y = R * oct[v] - p[k];
            double l0 = Det3(y, b, d) / det;
            double l1 = Det3(a, y, d) / det;
            double l2 = Det3(a, b, y) / det;
            double l3 = 1.0 - l0 - l1 - l2;
            if (l0 < -1e-6 || l1 < -1e-6 || l2 < -1e-6 || l3 < -1e-6) {
              ok = false;
              break;
            }
          }
          if (ok) {
            // Find max c_val
            double lo = 0.0005, hi = 0.008;
            for (int it = 0; it < 12; it++) {
              double mid = 0.5 * (lo + hi);
              double s_m = (mid + delta) / c_cone;
              vec3 p0_m = s_m * u0;
              double R_m = 1.75 * (mid + delta);
              vec3 am = p0_m - p[k];
              double det_m = Det3(am, b, d);
              if (std::abs(det_m) < 1e-12) { hi = mid; continue; }
              bool m_ok = true;
              for (int v = 0; v < 6; v++) {
                vec3 y = R_m * oct[v] - p[k];
                double l0 = Det3(y, b, d) / det_m;
                double l1 = Det3(am, y, d) / det_m;
                double l2 = Det3(am, b, y) / det_m;
                double l3 = 1.0 - l0 - l1 - l2;
                if (l0 < -1e-6 || l1 < -1e-6 || l2 < -1e-6 || l3 < -1e-6) {
                  m_ok = false; break;
                }
              }
              if (m_ok) lo = mid; else hi = mid;
            }
            if (lo > best_c) {
              best_c = lo;
              best_triple[0] = orig_idx[i];
              best_triple[1] = orig_idx[j];
              best_triple[2] = orig_idx[k];
            }
          }
        }
      }
    }
    std::cout << "c_cone = " << c_cone << ": best c = " << best_c
              << " with (" << best_triple[0] << ", " << best_triple[1] << ", " << best_triple[2] << ")\n";
  }
  return 0;
}
