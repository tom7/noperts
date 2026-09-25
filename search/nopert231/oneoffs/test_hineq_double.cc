#include <iostream>
#include <iomanip>
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

  ContactInfo c_core_contacts[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  Tube229::AuditAxis(tri, c_core_contacts, &ax_core, &center_core, &delta_core, &err, BigRat(5, 1000));

  vec3 u = {center0.x.ToDouble() / ax0.B.ToDouble(),
            center0.y.ToDouble() / ax0.B.ToDouble(),
            center0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 v = {center_core.x.ToDouble() / ax_core.B.ToDouble(),
            center_core.y.ToDouble() / ax_core.B.ToDouble(),
            center_core.z.ToDouble() / ax_core.B.ToDouble()};

  double A = yocto::dot(u, u);
  double u_dot_v = yocto::dot(u, v);
  double lam = u_dot_v / A;
  vec3 w = v - u * lam;
  double B_w = yocto::dot(w, w);

  std::cout << std::setprecision(10);
  std::cout << "A (||u||^2) = " << A << "\n";
  std::cout << "||u|| = " << std::sqrt(A) << "\n";
  std::cout << "B_w (||w||^2) = " << B_w << "\n";
  std::cout << "lam = " << lam << "\n";
  std::cout << "u_dot_v = " << u_dot_v << "\n";
  std::cout << "angle(u, v) = " << std::acos(u_dot_v / (std::sqrt(A) * std::sqrt(yocto::dot(v, v)))) * 180.0 / M_PI << " deg\n";

  double val_c_core = 0.0003;

  for (double cc = 0.015; cc <= 0.045; cc += 0.002) {
    double margin = lam * cc - val_c_core;
    double lhs = B_w * (A - cc * cc);
    double rhs = A * margin * margin;
    std::cout << "c_cone = " << cc << " -> lhs=" << lhs
              << ", rhs=" << rhs
              << ", diff(rhs-lhs)=" << (rhs - lhs) << "\n";
  }

  return 0;
}
