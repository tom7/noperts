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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  // Core axis at 32.68 deg:
  ContactInfo core_c[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate core_ax; BigVecQ3 core_ctr; BigRat core_del;
  Tube229::AuditAxis(tri, core_c, &core_ax, &core_ctr, &core_del, &err, BigRat(0));
  vec3 uc = {core_ctr.x.ToDouble() / core_ax.B.ToDouble(),
             core_ctr.y.ToDouble() / core_ax.B.ToDouble(),
             core_ctr.z.ToDouble() / core_ax.B.ToDouble()};

  double norm_u0 = yocto::length(u0);
  double dot_u0_uc = yocto::dot(u0, uc);
  double lam = dot_u0_uc / (norm_u0 * norm_u0);
  vec3 w = uc - lam * u0;
  double norm_w = yocto::length(w);

  std::cout << "norm_u0 = " << norm_u0 << ", norm_w = " << norm_w << ", lam = " << lam << "\n";

  // Test c_cone in [0.038, 0.041]
  for (double c_cone = 0.0385; c_cone <= 0.0405; c_cone += 0.0005) {
    double c_core = 0.001;
    // hineq: norm_w^2 * (norm_u0^2 - c_cone^2) <= norm_u0^2 * (lam * c_cone - c_core)^2
    double lhs = norm_w * norm_w * (norm_u0 * norm_u0 - c_cone * c_cone);
    double rhs = norm_u0 * norm_u0 * std::pow(lam * c_cone - c_core, 2.0);
    std::cout << "c_cone = " << c_cone << ": lhs = " << lhs << ", rhs = " << rhs
              << " -> hineq " << (lhs <= rhs ? "PASSED (margin " + std::to_string(rhs - lhs) + ")" : "FAILED") << "\n";
  }

  return 0;
}
