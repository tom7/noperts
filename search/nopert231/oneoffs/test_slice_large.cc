#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
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
      std::string err;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) valid_axes.push_back({cert, ctr, del});
      }
    }
  }

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  std::cout << std::setprecision(10);
  for (int step = 0; step <= 50; step += 5) {
    double t = step * 1e-4;
    double X = 18.6877 + t;
    double Y = -23.5388 - t;
    vec3 p = P0 + X * E1 + Y * E2;
    vec3 a = yocto::normalize(p);
    double best_dot = -1.0;
    int best_idx = -1;
    for (size_t i = 0; i < valid_axes.size(); i++) {
      vec3 vi = {valid_axes[i].center.x.ToDouble() / valid_axes[i].cert.B.ToDouble(),
                 valid_axes[i].center.y.ToDouble() / valid_axes[i].cert.B.ToDouble(),
                 valid_axes[i].center.z.ToDouble() / valid_axes[i].cert.B.ToDouble()};
      double d = yocto::dot(a, vi);
      if (d > best_dot) {
        best_dot = d;
        best_idx = i;
      }
    }
    std::cout << "t=" << t << " best=" << best_dot << " (axis " << best_idx << ")\n";
  }

  return 0;
}
