#include <iostream>
#include <string>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;

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

  std::string err;
  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 ctr0, ctr1, ctr2, ctr3;
  BigRat del0, del1, del2, del3;

  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(), ctr1.y.ToDouble() / ax1.B.ToDouble(), ctr1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 u2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(), ctr2.y.ToDouble() / ax2.B.ToDouble(), ctr2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 u3 = {ctr3.x.ToDouble() / ax3.B.ToDouble(), ctr3.y.ToDouble() / ax3.B.ToDouble(), ctr3.z.ToDouble() / ax3.B.ToDouble()};

  vec3 u0_hat = yocto::normalize(u0);

  // Basis for plane orthogonal to u0:
  vec3 e1;
  if (std::abs(u0_hat.x) < 0.5) e1 = yocto::normalize(yocto::cross(u0_hat, vec3{1, 0, 0}));
  else e1 = yocto::normalize(yocto::cross(u0_hat, vec3{0, 1, 0}));
  vec3 e2 = yocto::cross(u0_hat, e1);

  // 2D coordinates of u1, u2, u3 in this plane:
  vec2 p1 = {yocto::dot(u1, e1), yocto::dot(u1, e2)};
  vec2 p2 = {yocto::dot(u2, e1), yocto::dot(u2, e2)};
  vec2 p3 = {yocto::dot(u3, e1), yocto::dot(u3, e2)};

  std::cout << "2D points:\n";
  std::cout << "  p1 = (" << p1.x << ", " << p1.y << "), |p1| = " << yocto::length(p1) << "\n";
  std::cout << "  p2 = (" << p2.x << ", " << p2.y << "), |p2| = " << yocto::length(p2) << "\n";
  std::cout << "  p3 = (" << p3.x << ", " << p3.y << "), |p3| = " << yocto::length(p3) << "\n";

  // Distances from 2D origin to the 3 edges:
  vec2 pts[3] = {p1, p2, p3};
  for (int edge = 0; edge < 3; edge++) {
    vec2 a = pts[edge];
    vec2 b = pts[(edge + 1) % 3];
    // line through a, b: normal n = (-(b.y - a.y), b.x - a.x)
    vec2 n = {-(b.y - a.y), b.x - a.x};
    double n_len = yocto::length(n);
    n = n / n_len;
    double d = yocto::dot(a, n);
    if (d < 0) {
      n = -n;
      d = -d;
    }
    // Check which side 3rd point is on:
    vec2 c = pts[(edge + 2) % 3];
    double c_side = yocto::dot(c, n) - d;
    std::cout << "Edge " << edge << ": distance from (0,0) = " << d << ", opposite point side = " << c_side << "\n";
  }

  return 0;
}
