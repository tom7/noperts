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

  // Look at u0 and v directly from ctr0 and ax.center (which are evals / B)
  MyVec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ") norm=" << std::sqrt(u0.norm_sq()) << "\n";

  const auto &ax = valid_axes[2960];
  MyVec3 v = {ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()};
  std::cout << "v 2960: (" << v.x << ", " << v.y << ", " << v.z << ") norm=" << std::sqrt(v.norm_sq()) << "\n";

  double dot_v_u0 = v.dot(u0);
  double lam = dot_v_u0 / u0.norm_sq();
  MyVec3 w = {v.x - lam * u0.x, v.y - lam * u0.y, v.z - lam * u0.z};
  std::cout << "lam: " << lam << "\n";
  std::cout << "w norm: " << std::sqrt(w.norm_sq()) << "\n";

  double c_cone = 0.035;
  double c_core = 0.00055;
  double lhs = w.norm_sq() * (u0.norm_sq() - c_cone * c_cone);
  double rhs = u0.norm_sq() * (lam * c_cone - c_core) * (lam * c_cone - c_core);
  std::cout << "lam * c_cone - c_core = " << lam * c_cone - c_core << "\n";
  std::cout << "lhs = " << lhs << ", rhs = " << rhs << " (lhs <= rhs: " << (lhs <= rhs) << ")\n";
  return 0;
}
