#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0_sq = yocto::dot(u0, u0);

  vec3 E1 = vec3{1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = vec3{0.0, 1.0, -u0.y / u0.z};

  double c_cone = 0.035;
  double R_sq = 1.0 / (c_cone * c_cone) - 1.0 / norm_u0_sq;
  std::cout << "R_sq = " << R_sq << "\n";

  // Check the 3 vertices with min norm: (16.5, -11), (11, -16.5), (16.5, -16.5)
  auto norm_sq = [&](double X, double Y) {
    vec3 V = X * E1 + Y * E2;
    return yocto::dot(V, V);
  };

  std::cout << "norm_sq(16.5, -11) = " << norm_sq(16.5, -11) << "\n";
  std::cout << "norm_sq(11, -16.5) = " << norm_sq(11, -16.5) << "\n";
  std::cout << "norm_sq(16.5, -16.5) = " << norm_sq(16.5, -16.5) << "\n";

  // Also min on segment from (11, -16.5) to (16.5, -11):
  double min_seg = 1e9;
  for (int i = 0; i <= 1000; i++) {
    double t = i / 1000.0;
    double X = (1 - t) * 11.0 + t * 16.5;
    double Y = (1 - t) * (-16.5) + t * (-11.0);
    double ns = norm_sq(X, Y);
    if (ns < min_seg) min_seg = ns;
  }
  std::cout << "min on boundary segment = " << min_seg << "\n";

  return 0;
}
