#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

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

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = yocto::length(u0);
  vec3 u0_hat = u0 / norm_u0;

  vec3 k1 = vec3{1.0, 0.0, -u0.x / u0.z};
  k1 = k1 - yocto::dot(k1, u0_hat) * u0_hat;
  k1 = k1 / yocto::length(k1);
  vec3 k2 = yocto::cross(u0_hat, k1);

  double c_cone = 0.035;
  double c_core = 0.00055;
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

  int a = 2960;
  std::cout << "Total valid axes: " << valid_axes.size() << "\n";
  if (a >= (int)valid_axes.size()) {
    std::cout << "Index out of range\n";
    return 1;
  }
  const auto &ax = valid_axes[a];
  vec3 v = vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
  double c1 = yocto::dot(v, k1);
  double c2 = yocto::dot(v, k2);
  double c0 = yocto::dot(v, u0_hat) / norm_u0;

  double S = 11.0 / 16.0;
  double min_x = (c1 >= 0) ? -c1 * S : c1 * S;
  double min_y = (c2 >= 0) ? -c2 * S : c2 * S;
  double worst = min_x + min_y + c0 * c_cone;

  std::cout << "Axis " << a << ":\n";
  std::cout << "  c1 = " << c1 << "\n";
  std::cout << "  c2 = " << c2 << "\n";
  std::cout << "  c0 = " << c0 << "\n";
  std::cout << "  c0 * c_cone = " << c0 * c_cone << "\n";
  std::cout << "  min_x = " << min_x << ", min_y = " << min_y << "\n";
  std::cout << "  worst corner = " << worst << " (c_core = " << c_core << ")\n";
  std::cout << "  margin = " << worst - c_core << "\n";
  std::cout << "  delta = " << ax.delta.ToDouble() << "\n";
  std::cout << "  B = " << ax.cert.B.ToDouble() << "\n";

  return 0;
}
