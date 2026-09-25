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

  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_cert, &core_center, &core_delta, &err, BigRat(0));
  vec3 v_core = {core_center.x.ToDouble() / core_cert.B.ToDouble(),
                 core_center.y.ToDouble() / core_cert.B.ToDouble(),
                 core_center.z.ToDouble() / core_cert.B.ToDouble()};

  std::cout << "|u0| = " << yocto::length(u0) << "\n";
  std::cout << "|v_core| = " << yocto::length(v_core) << "\n";
  std::cout << "cos(u0, v_core) = " << yocto::dot(yocto::normalize(u0), yocto::normalize(v_core)) << "\n";

  // Check min of dot(a, v_core) when dot(a, u0) >= 0.005:
  // Analytically: the worst point a in dot(a, u0) >= 0.005
  // has dot(a, u_hat) = 0.005 / |u0| = cos(theta_0)
  // and points away from v_core as much as possible!
  // In the plane of u0 and v_core:
  // a = cos(theta_0) u_hat - sin(theta_0) w_hat
  // Then dot(a, v_core) = |v_core| * (cos(theta_0) cos(psi) - sin(theta_0) sin(psi))
  // = |v_core| * cos(theta_0 + psi)!
  double u_len = yocto::length(u0);
  double v_len = yocto::length(v_core);
  double psi = std::acos(yocto::dot(yocto::normalize(u0), yocto::normalize(v_core))); // 37.2 deg
  double cos_theta0 = 0.005 / u_len; // 0.005 / 0.0511 = 0.0978 => theta0 = 84.4 deg
  double theta0 = std::acos(cos_theta0);
  double worst_angle = theta0 + psi; // 84.4 + 37.2 = 121.6 deg!
  double worst_dot = v_len * std::cos(worst_angle);

  std::cout << "psi = " << psi * 180.0 / M_PI << " deg\n";
  std::cout << "theta0 = " << theta0 * 180.0 / M_PI << " deg\n";
  std::cout << "worst_angle = " << worst_angle * 180.0 / M_PI << " deg\n";
  std::cout << "worst dot(a, v_core) = " << worst_dot << "\n";

  return 0;
}
