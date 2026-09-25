#include <iostream>
#include <iomanip>
#include <algorithm>
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

  auto dist_sq_to_segment = [&](double px, double py, double qx, double qy) {
    vec3 V0 = px * E1 + py * E2;
    vec3 dV = (qx - px) * E1 + (qy - py) * E2;
    double dV_sq = yocto::dot(dV, dV);
    if (dV_sq < 1e-15) return yocto::dot(V0, V0);
    double t = -yocto::dot(V0, dV) / dV_sq;
    t = std::max(0.0, std::min(1.0, t));
    vec3 Vt = V0 + t * dV;
    return yocto::dot(Vt, Vt);
  };

  auto test_tri = [&](std::string name, double x1, double y1, double x2, double y2, double x3, double y3) {
    double d1 = dist_sq_to_segment(x1, y1, x2, y2);
    double d2 = dist_sq_to_segment(x2, y2, x3, y3);
    double d3 = dist_sq_to_segment(x3, y3, x1, y1);
    double min_d = std::min({d1, d2, d3});
    std::cout << name << ": min_d_sq = " << min_d << " (R_sq=" << R_sq << "), outside=" << (min_d > R_sq) << "\n";
  };

  test_tri("Pruned 1", 22, -22, 22, -11, 11, -22);
  test_tri("Pruned 2", 22, -11, 16.5, -11, 16.5, -16.5);
  test_tri("Pruned 3", 11, -22, 16.5, -16.5, 11, -16.5);

  return 0;
}
