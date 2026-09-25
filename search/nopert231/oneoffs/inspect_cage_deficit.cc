#include <iostream>
#include <vector>
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
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int idx1 = 1283, idx2 = 4074, idx3 = 1041;
  vec3 u1 = {base_axes[idx1].center.x.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.y.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.z.ToDouble() / base_axes[idx1].cert.B.ToDouble()};
  vec3 u2 = {base_axes[idx2].center.x.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.y.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.z.ToDouble() / base_axes[idx2].cert.B.ToDouble()};
  vec3 u3 = {base_axes[idx3].center.x.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.y.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.z.ToDouble() / base_axes[idx3].cert.B.ToDouble()};

  double delta = 0.000234013;
  double c_cone = 0.028;
  double box_c = 0.0002;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
  double det = yocto::dot(d1, yocto::cross(d2, d3));
  vec3 c23 = yocto::cross(d2, d3);

  for (int k = 0; k < 6; k++) {
    vec3 dp = oct[k] - v0;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
    double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    std::cout << "k=" << k << ": l0=" << l0 << ", l1=" << l1 << ", l2=" << l2 << ", l3=" << l3 << "\n";
  }

  return 0;
}
