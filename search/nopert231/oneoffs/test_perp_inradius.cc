#include <iostream>
#include <string>
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

  // Perpendicular components:
  vec3 u1_perp = u1 - u0_hat * yocto::dot(u1, u0_hat);
  vec3 u2_perp = u2 - u0_hat * yocto::dot(u2, u0_hat);
  vec3 u3_perp = u3 - u0_hat * yocto::dot(u3, u0_hat);

  std::cout << "Parallel components (u_j . u0_hat):\n";
  std::cout << "  u1_par = " << yocto::dot(u1, u0_hat) << "\n";
  std::cout << "  u2_par = " << yocto::dot(u2, u0_hat) << "\n";
  std::cout << "  u3_par = " << yocto::dot(u3, u0_hat) << "\n";

  std::cout << "Perpendicular lengths |u_j_perp|:\n";
  std::cout << "  |u1_perp| = " << yocto::length(u1_perp) << "\n";
  std::cout << "  |u2_perp| = " << yocto::length(u2_perp) << "\n";
  std::cout << "  |u3_perp| = " << yocto::length(u3_perp) << "\n";

  // Angles between perp components:
  double d12 = yocto::dot(yocto::normalize(u1_perp), yocto::normalize(u2_perp));
  double d23 = yocto::dot(yocto::normalize(u2_perp), yocto::normalize(u3_perp));
  double d31 = yocto::dot(yocto::normalize(u3_perp), yocto::normalize(u1_perp));
  std::cout << "Cosine of angles between perp vectors:\n";
  std::cout << "  cos(1, 2) = " << d12 << "\n";
  std::cout << "  cos(2, 3) = " << d23 << "\n";
  std::cout << "  cos(3, 1) = " << d31 << "\n";

  return 0;
}
