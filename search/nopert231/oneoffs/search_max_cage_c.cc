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

  double c_cone = 0.015;
  double delta = 0.000234013;

  auto det4 = [](const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d) {
    auto d3 = [](const vec3 &x, const vec3 &y, const vec3 &z) {
      return yocto::dot(x, yocto::cross(y, z));
    };
    return -d3(b, c, d) + d3(a, c, d) - d3(a, b, d) + d3(a, b, c);
  };

  auto test_c = [&](double c_val, const vec3 &p1, const vec3 &p2, const vec3 &p3) -> bool {
    double s = (c_val + delta) / c_cone;
    vec3 p0 = s * u0;
    double R = 1.75 * (c_val + delta);
    vec3 oct[6] = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
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

  std::vector<vec3> p(axes.size());
  for (size_t i = 0; i < axes.size(); i++) {
    p[i] = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
            axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
            axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
  }

  double best_c = 0.0030;
  int best_triple[3] = {-1, -1, -1};

  std::cout << "Searching over " << axes.size() << " axes...\n";
  for (size_t i = 0; i < axes.size(); i++) {
    for (size_t j = i + 1; j < axes.size(); j++) {
      for (size_t k = j + 1; k < axes.size(); k++) {
        if (test_c(best_c + 0.0001, p[i], p[j], p[k])) {
          double lo = best_c, hi = 0.015;
          for (int iter = 0; iter < 12; iter++) {
            double mid = 0.5 * (lo + hi);
            if (test_c(mid, p[i], p[j], p[k])) lo = mid;
            else hi = mid;
          }
          if (lo > best_c) {
            best_c = lo;
            best_triple[0] = i; best_triple[1] = j; best_triple[2] = k;
            std::cout << "New best c = " << best_c << " with (" << i << ", " << j << ", " << k << ")\n";
          }
        }
      }
    }
  }

  std::cout << "Done! Best c = " << best_c << " with ("
            << best_triple[0] << ", " << best_triple[1] << ", " << best_triple[2] << ")\n";
  return 0;
}
