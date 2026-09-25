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
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  // Let's test the gap point:
  double X = 18.7029, Y = -23.5236;
  vec3 p = P0 + X * E1 + Y * E2;
  double norm_p = yocto::length(p);
  vec3 a_unit = p / norm_p;

  std::cout << "Target unit a: (" << a_unit.x << ", " << a_unit.y << ", " << a_unit.z << ")\n";

  double best_margin = -1e9;
  int best_m1 = -1, best_m2 = -1;
  double best_dot = 0, best_del = 0;

  for (int m1 = 0; m1 <= 1000; m1 += 10) {
    for (int m2 = 0; m2 <= 1000; m2 += 10) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        double d_val = del.ToDouble();
        vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                  ctr.y.ToDouble() / cert.B.ToDouble(),
                  ctr.z.ToDouble() / cert.B.ToDouble()};
        double dot_val = yocto::dot(a_unit, v);
        // We want dot_val - d_val to be positive!
        // That means the axis covers a_unit with net margin (dot_val - delta) > 0!
        double margin = dot_val - d_val;
        if (margin > best_margin) {
          best_margin = margin;
          best_m1 = m1;
          best_m2 = m2;
          best_dot = dot_val;
          best_del = d_val;
        }
      }
    }
  }

  std::cout << "Best net margin (dot - delta): " << best_margin << "\n";
  std::cout << "  m1 = " << best_m1 << ", m2 = " << best_m2 << "\n";
  std::cout << "  dot = " << best_dot << ", delta = " << best_del << "\n";

  return 0;
}
