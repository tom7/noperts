#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Pt2 { double x, y; };

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

  double c_cone = 0.017;
  double c_core = 0.000234060;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  double R = std::sqrt(R_sq);
  std::cout << "c_cone = " << c_cone << ", R = " << R << "\n";

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

  auto check_pt = [&](Pt2 pt, int a) {
    vec3 p = P0 + pt.x * E1 + pt.y * E2;
    vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                  valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
    return yocto::dot(p, v) >= c_core * yocto::length(p);
  };

  auto check_tri = [&](Pt2 p1, Pt2 p2, Pt2 p3) {
    for (size_t a = 0; a < valid_axes.size(); a++) {
      if (check_pt(p1, a) && check_pt(p2, a) && check_pt(p3, a)) return (int)a;
    }
    return -1;
  };

  int count = 0;
  auto subdivide = [&](auto& self, Pt2 p1, Pt2 p2, Pt2 p3, int depth) -> bool {
    int a = check_tri(p1, p2, p3);
    if (a >= 0) {
      count++;
      return true;
    }
    if (depth >= 10) return false;

    Pt2 m12 = {0.5 * (p1.x + p2.x), 0.5 * (p1.y + p2.y)};
    Pt2 m23 = {0.5 * (p2.x + p3.x), 0.5 * (p2.y + p3.y)};
    Pt2 m31 = {0.5 * (p3.x + p1.x), 0.5 * (p3.y + p1.y)};

    return self(self, p1, m12, m31, depth + 1) &&
           self(self, m12, p2, m23, depth + 1) &&
           self(self, m31, m23, p3, depth + 1) &&
           self(self, m12, m23, m31, depth + 1);
  };

  // Start with a regular N-gon circumscribing D(0, R):
  // Vertices at R_circ = R / cos(pi / N)
  // Connect each edge to origin (0,0)
  int N = 12;
  double R_circ = R / std::cos(M_PI / N);
  std::vector<Pt2> poly(N);
  for (int k = 0; k < N; k++) {
    double th = k * 2.0 * M_PI / N;
    poly[k] = {R_circ * std::cos(th), R_circ * std::sin(th)};
  }

  Pt2 origin = {0, 0};
  bool all_ok = true;
  for (int k = 0; k < N; k++) {
    int next = (k + 1) % N;
    if (!subdivide(subdivide, origin, poly[k], poly[next], 0)) {
      std::cout << "Sector " << k << " failed!\n";
      all_ok = false;
      break;
    }
  }

  std::cout << "Subdivision result: all_ok = " << all_ok << ", leaves = " << count << "\n";
  return 0;
}
