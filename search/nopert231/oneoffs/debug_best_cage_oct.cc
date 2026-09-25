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
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  double delta = 0.000234013;
  double box_c = 0.001;
  double c_cone = 0.020;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  // Check the old winning canyon axes: 1, 2, 3
  // What are their indices in base_axes?
  // Let's print the barycentric coords for c_cone = 0.020 with the old axes:
  // ax1: (0.0414995, -0.00843135, 0.0305602)
  // ax2: (-0.00552695, -0.0101968, 0.00412852)
  // ax3: (-0.00762334, 0.0537446, -0.0118833)
  vec3 v1 = {0.0414995, -0.00843135, 0.0305602};
  vec3 v2 = {-0.00552695, -0.0101968, 0.00412852};
  vec3 v3 = {-0.00762334, 0.0537446, -0.0118833};

  vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
  double det = yocto::dot(d1, yocto::cross(d2, d3));
  vec3 c23 = yocto::cross(d2, d3);

  std::cout << "det = " << det << "\n";
  for (int p_idx = 0; p_idx < 6; p_idx++) {
    vec3 dp = oct[p_idx] - v0;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
    double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    std::cout << "Oct vertex " << p_idx << ": l0=" << l0 << ", l1=" << l1
              << ", l2=" << l2 << ", l3=" << l3
              << " (min = " << std::min({l0, l1, l2, l3}) << ")\n";
  }

  return 0;
}
