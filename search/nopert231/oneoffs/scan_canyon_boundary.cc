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
  for (int m1 = 300; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 400; m2 += 25) {
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

  double c_core = 0.000234060;
  std::cout << "Scanning outward from canyon along (dX, dY) = (1, 1)...\n";
  for (double step = -0.05; step <= 0.05; step += 0.005) {
    double X = 18.6879 + step;
    double Y = -23.5386 + step;
    vec3 p = P0 + X * E1 + Y * E2;
    vec3 a = yocto::normalize(p);

    int best_ax = -1;
    double best_dot = -1.0;
    for (size_t i = 0; i < valid_axes.size(); i++) {
      vec3 v = {valid_axes[i].center.x.ToDouble() / valid_axes[i].cert.B.ToDouble(),
                valid_axes[i].center.y.ToDouble() / valid_axes[i].cert.B.ToDouble(),
                valid_axes[i].center.z.ToDouble() / valid_axes[i].cert.B.ToDouble()};
      double d = yocto::dot(a, v);
      if (d > best_dot) {
        best_dot = d;
        best_ax = i;
      }
    }
    std::cout << "step=" << std::setw(6) << step
              << " (X=" << X << ", Y=" << Y << "): best axis " << best_ax
              << " dot=" << best_dot
              << (best_dot >= c_core ? " [COVERED]" : " [GAP!]") << "\n";
  }

  return 0;
}
