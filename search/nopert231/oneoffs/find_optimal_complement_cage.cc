#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

BigRat Det4(const BigRat m[4][4]) {
  BigRat a = m[0][0], b = m[0][1], c = m[0][2], d = m[0][3];
  BigRat e = m[1][0], f = m[1][1], g = m[1][2], h = m[1][3];
  BigRat i = m[2][0], j = m[2][1], k = m[2][2], l = m[2][3];
  BigRat n = m[3][0], o = m[3][1], p = m[3][2], q = m[3][3];

  BigRat kp_lo = k * q - l * p;
  BigRat jp_ln = j * q - l * o;
  BigRat jo_kn = j * p - k * o;
  BigRat ip_lm = i * q - l * n;
  BigRat io_km = i * p - k * n;
  BigRat in_jm = i * o - j * n;

  BigRat d1 = f * kp_lo - g * jp_ln + h * jo_kn;
  BigRat d2 = e * kp_lo - g * ip_lm + h * io_km;
  BigRat d3 = e * jp_ln - f * ip_lm + h * in_jm;
  BigRat d4 = e * jo_kn - f * io_km + g * in_jm;

  return a * d1 - b * d2 + c * d3 - d * d4;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);

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
  vec3 dir_u0 = yocto::normalize(u0);

  // Filter axes that have good angle to u0 (e.g. dot with u0 between -0.5 and 0.5):
  std::vector<size_t> filtered;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(yocto::normalize(v), dir_u0);
    if (d < 0.2) filtered.push_back(i);
  }
  std::cout << "Filtered to " << filtered.size() << " candidate complement axes\n";

  // Test triples in double precision:
  double c_cone = 0.015;
  double delta = 0.000234013;

  double best_c = 0.0;
  int best_triple[3] = {-1, -1, -1};

  auto test_c = [&](double c_val, const vec3 &p1, const vec3 &p2, const vec3 &p3) -> bool {
    double s = (c_val + delta) / c_cone;
    vec3 p0 = s * u0;
    double R = 1.75 * (c_val + delta);
    vec3 oct[6] = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };
    // Det of [p0, p1, p2, p3; 1, 1, 1, 1]
    auto det4 = [](const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d) {
      // expand along bottom row [1, 1, 1, 1]
      auto d3 = [](const vec3 &x, const vec3 &y, const vec3 &z) {
        return yocto::dot(x, yocto::cross(y, z));
      };
      return -d3(b, c, d) + d3(a, c, d) - d3(a, b, d) + d3(a, b, c);
    };
    double D = det4(p0, p1, p2, p3);
    if (D <= 1e-9) return false;

    for (int k = 0; k < 6; k++) {
      double l0 = det4(oct[k], p1, p2, p3) / D;
      double l1 = det4(p0, oct[k], p2, p3) / D;
      double l2 = det4(p0, p1, oct[k], p3) / D;
      double l3 = det4(p0, p1, p2, oct[k]) / D;
      if (l0 <= 1e-6 || l1 <= 1e-6 || l2 <= 1e-6 || l3 <= 1e-6) return false;
    }
    return true;
  };

  for (size_t i = 0; i < filtered.size(); i++) {
    vec3 p1 = {axes[filtered[i]].center.x.ToDouble() / axes[filtered[i]].cert.B.ToDouble(),
               axes[filtered[i]].center.y.ToDouble() / axes[filtered[i]].cert.B.ToDouble(),
               axes[filtered[i]].center.z.ToDouble() / axes[filtered[i]].cert.B.ToDouble()};
    for (size_t j = i + 1; j < filtered.size(); j++) {
      vec3 p2 = {axes[filtered[j]].center.x.ToDouble() / axes[filtered[j]].cert.B.ToDouble(),
                 axes[filtered[j]].center.y.ToDouble() / axes[filtered[j]].cert.B.ToDouble(),
                 axes[filtered[j]].center.z.ToDouble() / axes[filtered[j]].cert.B.ToDouble()};
      for (size_t k = j + 1; k < filtered.size(); k++) {
        vec3 p3 = {axes[filtered[k]].center.x.ToDouble() / axes[filtered[k]].cert.B.ToDouble(),
                   axes[filtered[k]].center.y.ToDouble() / axes[filtered[k]].cert.B.ToDouble(),
                   axes[filtered[k]].center.z.ToDouble() / axes[filtered[k]].cert.B.ToDouble()};

        if (test_c(0.0050, p1, p2, p3)) {
          // Find max c for this triple:
          double lo = 0.0050, hi = 0.0150;
          for (int iter = 0; iter < 10; iter++) {
            double mid = 0.5 * (lo + hi);
            if (test_c(mid, p1, p2, p3)) lo = mid;
            else hi = mid;
          }
          if (lo > best_c) {
            best_c = lo;
            best_triple[0] = filtered[i];
            best_triple[1] = filtered[j];
            best_triple[2] = filtered[k];
            std::cout << "New best c = " << best_c << " with triple ("
                      << filtered[i] << ", " << filtered[j] << ", " << filtered[k] << ")\n";
          }
        }
      }
    }
  }

  std::cout << "Overall best c = " << best_c << " with triple ("
            << best_triple[0] << ", " << best_triple[1] << ", " << best_triple[2] << ")\n";
  return 0;
}
