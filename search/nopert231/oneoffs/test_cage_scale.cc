#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  int b1 = 0, b2 = 24, b3 = 136;
  const auto &ax1 = axes[b1];
  const auto &ax2 = axes[b2];
  const auto &ax3 = axes[b3];

  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u1 = {ax1.center.x.ToDouble() / ax1.cert.B.ToDouble(), ax1.center.y.ToDouble() / ax1.cert.B.ToDouble(), ax1.center.z.ToDouble() / ax1.cert.B.ToDouble()};
  vec3 u2 = {ax2.center.x.ToDouble() / ax2.cert.B.ToDouble(), ax2.center.y.ToDouble() / ax2.cert.B.ToDouble(), ax2.center.z.ToDouble() / ax2.cert.B.ToDouble()};
  vec3 u3 = {ax3.center.x.ToDouble() / ax3.cert.B.ToDouble(), ax3.center.y.ToDouble() / ax3.cert.B.ToDouble(), ax3.center.z.ToDouble() / ax3.cert.B.ToDouble()};

  std::cout << "det(u1, u2, u3) = " << yocto::dot(u1, yocto::cross(u2, u3)) << "\n";

  for (double c_cone : {0.010, 0.012, 0.015, 0.018, 0.020, 0.025, 0.030}) {
    for (double box_c : {0.0001, 0.0002, 0.0003, 0.0004, 0.0005}) {
      double delta = 0.000234;
      double s = (box_c + delta) / c_cone;
      double R = 1.75 * (box_c + delta);
      vec3 v0 = u0 * s;
      vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
      double det = yocto::dot(d1, yocto::cross(d2, d3));
      if (std::abs(det) < 1e-8) continue;
      vec3 c23 = yocto::cross(d2, d3);

      std::vector<vec3> oct = {
        {R, 0, 0}, {-R, 0, 0},
        {0, R, 0}, {0, -R, 0},
        {0, 0, R}, {0, 0, -R}
      };
      double min_l = 1e9;
      for (const auto &p : oct) {
        vec3 dp = p - v0;
        double l1 = yocto::dot(dp, c23) / det;
        double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
        double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
        double l0 = 1.0 - l1 - l2 - l3;
        min_l = std::min({min_l, l0, l1, l2, l3});
      }
      if (min_l > 0) {
        std::cout << "c_cone=" << c_cone << " box_c=" << box_c << " s=" << s << " -> min_l=" << min_l << "\n";
      }
    }
  }


  return 0;
}
