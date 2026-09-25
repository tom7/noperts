#include <iostream>
#include <vector>
#include <cmath>
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

  auto check_pt = [&](Pt2 pt) {
    vec3 p = P0 + pt.x * E1 + pt.y * E2;
    for (size_t a = 0; a < valid_axes.size(); a++) {
      vec3 v = vec3{valid_axes[a].center.x.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                    valid_axes[a].center.y.ToDouble() / valid_axes[a].cert.B.ToDouble(),
                    valid_axes[a].center.z.ToDouble() / valid_axes[a].cert.B.ToDouble()};
      if (yocto::dot(p, v) >= c_core * yocto::length(p)) return (int)a;
    }
    return -1;
  };

  int N = 12;
  double R_circ = R / std::cos(M_PI / N);
  double th10 = 10 * 2.0 * M_PI / N;
  double th11 = 11 * 2.0 * M_PI / N;
  Pt2 p1 = {R_circ * std::cos(th10), R_circ * std::sin(th10)};
  Pt2 p2 = {R_circ * std::cos(th11), R_circ * std::sin(th11)};

  std::cout << "p1 = (" << p1.x << ", " << p1.y << "), axis = " << check_pt(p1) << "\n";
  std::cout << "p2 = (" << p2.x << ", " << p2.y << "), axis = " << check_pt(p2) << "\n";

  // Check along edge p1..p2
  for (int step = 0; step <= 20; step++) {
    double t = step / 20.0;
    Pt2 pt = {(1 - t) * p1.x + t * p2.x, (1 - t) * p1.y + t * p2.y};
    double r = std::sqrt(pt.x * pt.x + pt.y * pt.y);
    int ax = check_pt(pt);
    std::cout << "t = " << t << ", r = " << r << " (R=" << R << "), axis = " << ax << "\n";
  }

  return 0;
}
