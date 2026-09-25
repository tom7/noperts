#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(2, 1, 1, 4, 333, 1)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 666, 15),
    MakeContact(3, 2, 2, 1, 0, 2)
  };
  ContactInfo c3[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(1, 4, 4, 8, 333, 4),
    MakeContact(15, 19, 19, 3, 1000, 19)
  };

  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 center0, center1, center2, center3;
  BigRat delta0, delta1, delta2, delta3;
  std::string err;

  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &center1, &delta1, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &ax2, &center2, &delta2, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &ax3, &center3, &delta3, &err, BigRat(5, 1000));

  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 v1 = {center1.x.ToDouble() / ax1.B.ToDouble(),
             center1.y.ToDouble() / ax1.B.ToDouble(),
             center1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 v2 = {center2.x.ToDouble() / ax2.B.ToDouble(),
             center2.y.ToDouble() / ax2.B.ToDouble(),
             center2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 v3 = {center3.x.ToDouble() / ax3.B.ToDouble(),
             center3.y.ToDouble() / ax3.B.ToDouble(),
             center3.z.ToDouble() / ax3.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.001;

  for (double c_cone = 0.015; c_cone <= 0.045; c_cone += 0.001) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);

    std::vector<vec3> oct = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };

    vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
    double det = yocto::dot(d1, yocto::cross(d2, d3));
    vec3 c23 = yocto::cross(d2, d3);

    double min_l = 1e9;
    for (const auto &p : oct) {
      vec3 dp = p - v0;
      double l1 = yocto::dot(dp, c23) / det;
      double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
      double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      min_l = std::min({min_l, l0, l1, l2, l3});
    }
    std::cout << "c_cone = " << c_cone << ": min_l = " << min_l << "\n";
  }

  return 0;
}
