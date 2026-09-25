#include <iostream>
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

  double B0 = ax0.B.ToDouble();
  vec3 u0 = {ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double u0_len_sq = yocto::dot(u0, u0);
  double delta = 3.33e-7;

  // Sibling axis c35 from earlier:
  ContactInfo c35[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax35;
  BigVecQ3 ctr35;
  BigRat del35;
  Tube229::AuditAxis(tri, c35, &ax35, &ctr35, &del35, &err, BigRat(0));
  vec3 u_core = {ctr35.x.ToDouble() / ax35.B.ToDouble(),
                 ctr35.y.ToDouble() / ax35.B.ToDouble(),
                 ctr35.z.ToDouble() / ax35.B.ToDouble()};
  double c_core = 0.002133;

  double lam = yocto::dot(u_core, u0) / u0_len_sq;
  vec3 w = u_core - u0 * lam;
  double w_len_sq = yocto::dot(w, w);

  std::cout << "lam = " << lam << ", |w|^2 = " << w_len_sq << ", |u0|^2 = " << u0_len_sq << "\n";

  for (double c_cone = 0.005; c_cone <= 0.040; c_cone += 0.005) {
    double lhs = w_len_sq * (u0_len_sq - c_cone * c_cone);
    double margin = lam * c_cone - c_core;
    double rhs = u0_len_sq * margin * margin;
    std::cout << "c_cone=" << c_cone << ": margin=" << margin << ", lhs=" << lhs << ", rhs=" << rhs << "\n";
  }

  return 0;
}
