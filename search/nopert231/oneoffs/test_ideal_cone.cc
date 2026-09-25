#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  double delta = 3.33e-7;
  double c_cone = 0.028;
  double box_c = 1e-7;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 axis = yocto::normalize(-u0);
  // Find two orthonormal vectors perpendicular to axis:
  vec3 perp1 = yocto::normalize(yocto::cross(axis, vec3{1, 0, 0}));
  if (yocto::length(yocto::cross(axis, vec3{1, 0, 0})) < 0.1) {
    perp1 = yocto::normalize(yocto::cross(axis, vec3{0, 1, 0}));
  }
  vec3 perp2 = yocto::cross(axis, perp1);

  // Test ideal directions at angle theta from axis, spaced at 120 degrees:
  for (double angle_deg = 75.0; angle_deg <= 88.0; angle_deg += 1.0) {
    double rad = angle_deg * M_PI / 180.0;
    double ca = std::cos(rad);
    double sa = std::sin(rad);

    vec3 u1 = (axis * ca + perp1 * sa) * 0.04;
    vec3 u2 = (axis * ca + (perp1 * (-0.5) + perp2 * (std::sqrt(3.0)/2.0)) * sa) * 0.04;
    vec3 u3 = (axis * ca + (perp1 * (-0.5) - perp2 * (std::sqrt(3.0)/2.0)) * sa) * 0.04;

    vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
    double det = yocto::dot(d1, yocto::cross(d2, d3));
    vec3 c23 = yocto::cross(d2, d3);
    vec3 c31 = yocto::cross(d3, d1);
    vec3 c12 = yocto::cross(d1, d2);

    double min_l = 1e9;
    for (const auto &p : oct) {
      vec3 dp = p - v0;
      double l1 = yocto::dot(dp, c23) / det;
      double l2 = yocto::dot(dp, c31) / det;
      double l3 = yocto::dot(dp, c12) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      min_l = std::min({min_l, l0, l1, l2, l3});
    }

    std::cout << "Angle " << angle_deg << " deg: min_l = " << min_l << "\n";
  }

  return 0;
}
