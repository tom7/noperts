#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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
  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);

  vec3 E1 = vec3{1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = vec3{0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);

  double box_delta = 234013.0 / 1000000000.0;
  std::vector<Tube229::AuditedAxis> valid_axes;
  for (const auto &ax : axes) {
    if (ax.delta.ToDouble() <= box_delta) valid_axes.push_back(ax);
  }

  // Also include grid axes
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

  std::cout << "Testing sample of points inside disk D(0, " << R << "):\n";
  int total_pts = 0;
  int uncovered = 0;
  for (double r = 0; r <= R; r += 2.0) {
    int num_ang = (r == 0 ? 1 : (int)(r * 3.0));
    for (int k = 0; k < num_ang; k++) {
      double th = k * 2.0 * M_PI / num_ang;
      double X = r * std::cos(th);
      double Y = r * std::sin(th);
      vec3 p = P0 + X * E1 + Y * E2;
      double len_p = yocto::length(p);

      bool covered = false;
      for (size_t a = 0; a < valid_axes.size(); a++) {
        vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                      valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                      valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
        if (yocto::dot(p, v) >= c_core * len_p) {
          covered = true; break;
        }
      }
      total_pts++;
      if (!covered) {
        uncovered++;
        if (uncovered <= 5) {
          std::cout << "Uncovered pt at r = " << r << ", th = " << th << " (X=" << X << ", Y=" << Y << ")\n";
        }
      }
    }
  }
  std::cout << "Total tested: " << total_pts << ", Uncovered: " << uncovered << "\n";
  return 0;
}
