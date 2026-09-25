#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  ContactInfo c_ann[3] = {{3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}};
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c_ann, &cert0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / cert0.B.ToDouble(),
             center0.y.ToDouble() / cert0.B.ToDouble(),
             center0.z.ToDouble() / cert0.B.ToDouble()};
  double u0_sq = yocto::dot(u0, u0);

  // Axis 1691:
  ContactInfo a1691[3] = {{15, 19, 19, 3, 900, 19}, {3, 2, 2, 1, 333, 2}, {4, 8, 8, 9, 1000, 8}};
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  Tube229::AuditAxis(tri, a1691, &cert, &center, &delta, &err, BigRat(0));
  vec3 v = {center.x.ToDouble() / cert.B.ToDouble(),
            center.y.ToDouble() / cert.B.ToDouble(),
            center.z.ToDouble() / cert.B.ToDouble()};

  double lam = yocto::dot(v, u0) / u0_sq;
  vec3 w = v - lam * u0;
  double w_sq = yocto::dot(w, w);
  double c_core = 0.001;

  std::cout << "lam = " << lam << ", |w|^2 = " << w_sq << ", |u0|^2 = " << u0_sq << "\n";
  std::cout << "|u0| = " << std::sqrt(u0_sq) << "\n";

  for (double c_cone = 0.0400; c_cone <= 0.0500; c_cone += 0.0005) {
    double margin = lam * c_cone - c_core;
    double lhs = w_sq * (u0_sq - c_cone * c_cone);
    double rhs = u0_sq * margin * margin;
    std::cout << "c_cone = " << c_cone << ": lhs=" << lhs << ", rhs=" << rhs
              << " -> " << (lhs <= rhs ? "PASS!" : "FAIL (ratio = " + std::to_string(lhs/rhs) + ")") << "\n";
  }

  return 0;
}
