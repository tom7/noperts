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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  AxisCertificate ax[4];
  BigVecQ3 ctr[4];
  BigRat del[4];
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax[0], &ctr[0], &del[0], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax[1], &ctr[1], &del[1], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &ax[2], &ctr[2], &del[2], &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &ax[3], &ctr[3], &del[3], &err, BigRat(5, 1000));

  vec3 u[4];
  for (int j = 0; j < 4; j++) {
    u[j] = {ctr[j].x.ToDouble() / ax[j].B.ToDouble(),
            ctr[j].y.ToDouble() / ax[j].B.ToDouble(),
            ctr[j].z.ToDouble() / ax[j].B.ToDouble()};
  }

  double delta = 0.000234013;
  double box_c = 0.0002; // or whatever c was in tree_0

  for (double c_cone = 0.010; c_cone <= 0.050; c_cone += 0.002) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u[0] * scale;
    double R = 1.75 * (box_c + delta);

    std::vector<vec3> oct = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };

    vec3 d1 = u[1] - v0, d2 = u[2] - v0, d3 = u[3] - v0;
    vec3 c12 = yocto::cross(d1, d2);
    double det = yocto::dot(c12, d3);
    vec3 c23 = yocto::cross(d2, d3);
    vec3 c31 = yocto::cross(d3, d1);

    double min_l = 1e9;
    for (const auto &p : oct) {
      vec3 dp = p - v0;
      double l1 = yocto::dot(dp, c23) / det;
      double l2 = yocto::dot(dp, c31) / det;
      double l3 = yocto::dot(dp, c12) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      double m = std::min({l0, l1, l2, l3});
      if (m < min_l) min_l = m;
    }
    std::cout << "c_cone = " << c_cone << ": min_l = " << min_l << "\n";
  }

  return 0;
}
