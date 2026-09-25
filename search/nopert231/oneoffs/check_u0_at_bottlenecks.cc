#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};
  double norm_u0 = std::sqrt(yocto::dot(u0, u0));
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  std::cout << "u0 norm: " << norm_u0 << "\n";

  // Check the points where the 2D quadtree struggled:
  // pt1: (0.919, 0.908)
  // pt2: (0.945, 1.085)
  // pt3: (0.962, 1.259)
  // pt4: (1.018, 1.096)
  double pts[4][2] = {
    {0.919, 0.908},
    {0.945, 1.085},
    {0.962, 1.259},
    {1.018, 1.096}
  };

  for (int i = 0; i < 4; i++) {
    double x = pts[i][0];
    double y = pts[i][1];
    vec3 a = yocto::normalize(x * k1 + y * k2 + e3);
    double dot_u0 = yocto::dot(a, u0);
    std::cout << "pt " << i << " (" << x << ", " << y << "): dot(a, u0) = " << dot_u0
              << ", norm_proj = " << std::sqrt(x*x + y*y)
              << ", cos(angle) = " << yocto::dot(a, e3) << "\n";
  }

  return 0;
}
