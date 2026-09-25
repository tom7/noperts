#include <iostream>
#include <vector>
#include <iomanip>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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

  double delta = 0.000234013;
  double box_c = 0.001;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  int idx1 = 421, idx2 = 1689, idx3 = 2933;
  vec3 v1 = {base_axes[idx1].center.x.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.y.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
             base_axes[idx1].center.z.ToDouble() / base_axes[idx1].cert.B.ToDouble()};
  vec3 v2 = {base_axes[idx2].center.x.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.y.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
             base_axes[idx2].center.z.ToDouble() / base_axes[idx2].cert.B.ToDouble()};
  vec3 v3 = {base_axes[idx3].center.x.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.y.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
             base_axes[idx3].center.z.ToDouble() / base_axes[idx3].cert.B.ToDouble()};

  double c_cone = 0.029;
  vec3 v0 = u0 * ((box_c + delta) / c_cone);
  vec3 d1 = v1 - v0;
  vec3 d2 = v2 - v0;
  vec3 d3 = v3 - v0;
  vec3 c12 = yocto::cross(d1, d2);
  vec3 c23 = yocto::cross(d2, d3);
  vec3 c31 = yocto::cross(d3, d1);
  double det = yocto::dot(c12, d3);

  std::cout << "v0: " << v0.x << ", " << v0.y << ", " << v0.z << "\n";
  std::cout << "R: " << R << "\n";
  std::cout << std::setprecision(8);
  for (int p = 0; p < 6; p++) {
    vec3 dp = oct[p] - v0;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(dp, c31) / det;
    double l3 = yocto::dot(dp, c12) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    std::cout << "Oct vertex " << p << ": l0=" << l0 << ", l1=" << l1
              << ", l2=" << l2 << ", l3=" << l3
              << " (min = " << std::min({l0, l1, l2, l3}) << ")\n";
  }

  return 0;
}
