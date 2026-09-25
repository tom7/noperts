#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

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

  // Best mixes from optimize_triple_mixes:
  // a1: (1, 200), (10, 270), (15, 200)
  // a2: (19, 290), (8, 600), (19, 600)
  // a3: (2, 130), (1, 420), (15, 800)
  ContactInfo a1[3] = {
    MakeContact(18, 1, 1, 5, 200, 1),
    MakeContact(9, 10, 10, 15, 270, 10),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo a2[3] = {
    MakeContact(15, 19, 19, 3, 290, 19),
    MakeContact(5, 8, 8, 9, 600, 8),
    MakeContact(15, 19, 19, 3, 600, 19)
  };
  ContactInfo a3[3] = {
    MakeContact(3, 2, 2, 1, 130, 2),
    MakeContact(2, 1, 1, 5, 420, 1),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  AxisCertificate cert1, cert2, cert3;
  BigVecQ3 ctr1, ctr2, ctr3;
  BigRat del1, del2, del3;
  Tube229::AuditAxis(tri, a1, &cert1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, a2, &cert2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, a3, &cert3, &ctr3, &del3, &err, BigRat(0));

  vec3 u1 = {ctr1.x.ToDouble() / cert1.B.ToDouble(), ctr1.y.ToDouble() / cert1.B.ToDouble(), ctr1.z.ToDouble() / cert1.B.ToDouble()};
  vec3 u2 = {ctr2.x.ToDouble() / cert2.B.ToDouble(), ctr2.y.ToDouble() / cert2.B.ToDouble(), ctr2.z.ToDouble() / cert2.B.ToDouble()};
  vec3 u3 = {ctr3.x.ToDouble() / cert3.B.ToDouble(), ctr3.y.ToDouble() / cert3.B.ToDouble(), ctr3.z.ToDouble() / cert3.B.ToDouble()};
  double delta = 3.33e-7;
  double box_c = 1e-7;
  std::vector<vec3> oct_dirs = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  for (double c_cone = 0.001; c_cone <= 0.030; c_cone += 0.001) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);

    vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
    vec3 c12 = yocto::cross(d1, d2);
    vec3 c23 = yocto::cross(d2, d3);
    vec3 c31 = yocto::cross(d3, d1);
    double det = yocto::dot(c12, d3);

    double min_l = 1e9;
    for (int m = 0; m < 6; m++) {
      vec3 dp = oct_dirs[m] * R - v0;
      double l1 = yocto::dot(dp, c23) / det;
      double l2 = yocto::dot(dp, c31) / det;
      double l3 = yocto::dot(dp, c12) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      double min_vert = std::min({l0, l1, l2, l3});
      if (min_vert < min_l) min_l = min_vert;
    }
    std::cout << "c_cone = " << c_cone << ": min_l = " << min_l << "\n";
  }

  return 0;
}
