#include <iostream>
#include <iomanip>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct MyVec3 {
  double x, y, z;
  double dot(const MyVec3 &o) const { return x*o.x + y*o.y + z*o.z; }
  double norm_sq() const { return dot(*this); }
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo contacts0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, contacts0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  MyVec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  std::cout << "Total valid axes: " << valid_axes.size() << "\n";

  // Test different c_cone values (must be >= box_delta and satisfy annular dominance)
  // Annular dominance for c_cone:
  // (1/2 * r^2 * B0 + D0)^2 <= r_min^2 * (1 - 1/4 * r^2) * ((c_cone - delta)^2 * B0^2)
  // For r=4e-5, B0=1.397, D0=0, delta=0.000234:
  // 1/2 * r^2 * B0 = 1/2 * 1.6e-9 * 1.397 = 1.1176e-9
  // (1.1176e-9)^2 = 1.25e-18
  // r_min = 5e-4 => r_min^2 = 2.5e-7
  // (c_cone - delta) * B0 >= 1.1176e-9 / (5e-4) = 2.235e-6
  // So almost ANY c_cone > delta satisfies annular dominance!
  // In fact, c_cone can be anything between 0.0005 and 0.070!

  for (double c_cone : {0.005, 0.010, 0.015, 0.020, 0.025, 0.030, 0.035, 0.040, 0.045, 0.050, 0.055, 0.060, 0.065, 0.070}) {
    if (u0.norm_sq() <= c_cone * c_cone) continue;
    double best_ratio = 1e9;
    int best_idx = -1;
    int win_count = 0;
    double c_core = 0.00055;

    for (size_t i = 0; i < valid_axes.size(); i++) {
      const auto &ax = valid_axes[i];
      MyVec3 v = {ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()};
      double dot_v_u0 = v.dot(u0);
      double lam = dot_v_u0 / u0.norm_sq();
      if (lam <= 0) continue;
      double margin = lam * c_cone - c_core;
      if (margin <= 0) continue;

      MyVec3 w = {v.x - lam * u0.x, v.y - lam * u0.y, v.z - lam * u0.z};
      double lhs = w.norm_sq() * (u0.norm_sq() - c_cone * c_cone);
      double rhs = u0.norm_sq() * margin * margin;
      double ratio = lhs / rhs;
      if (ratio < best_ratio) {
        best_ratio = ratio;
        best_idx = i;
      }
      if (ratio <= 1.0) {
        win_count++;
      }
    }
    std::cout << "c_cone=" << std::fixed << std::setprecision(3) << c_cone
              << ": best_ratio=" << std::setprecision(5) << best_ratio
              << " (axis " << best_idx << "), win_count=" << win_count << "\n";
  }
  return 0;
}
