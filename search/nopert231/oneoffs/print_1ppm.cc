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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 644, 15),
    MakeContact(3, 2, 2, 1, 0, 2)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 236, 1),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 540, 2),
    MakeContact(8, 9, 9, 10, 200, 9),
    MakeContact(3, 2, 2, 1, 541, 2)
  };

  std::string err;
  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 cnt0, cnt1, cnt2, cnt3;
  BigRat dlt0, dlt1, dlt2, dlt3;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &dlt0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &dlt1, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &ax2, &cnt2, &dlt2, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &ax3, &cnt3, &dlt3, &err, BigRat(5, 1000));

  vec3 u0 = {cnt0.x.ToDouble() / ax0.B.ToDouble(), cnt0.y.ToDouble() / ax0.B.ToDouble(), cnt0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 v1 = {cnt1.x.ToDouble() / ax1.B.ToDouble(), cnt1.y.ToDouble() / ax1.B.ToDouble(), cnt1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 v2 = {cnt2.x.ToDouble() / ax2.B.ToDouble(), cnt2.y.ToDouble() / ax2.B.ToDouble(), cnt2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 v3 = {cnt3.x.ToDouble() / ax3.B.ToDouble(), cnt3.y.ToDouble() / ax3.B.ToDouble(), cnt3.z.ToDouble() / ax3.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.000255;
  double c_cone = 0.0278;
  vec3 v0 = u0 * ((box_c + delta) / c_cone);

  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 d1 = v1 - v0;
  vec3 d2 = v2 - v0;
  vec3 d3 = v3 - v0;
  vec3 c12 = yocto::cross(d1, d2);
  vec3 c23 = yocto::cross(d2, d3);
  vec3 c31 = yocto::cross(d3, d1);
  double det = yocto::dot(c12, d3);

  std::cout << std::setprecision(10);
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
