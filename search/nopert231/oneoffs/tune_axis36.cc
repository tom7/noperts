#include <iostream>
#include <vector>
#include <cmath>
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

  double X = 18.6821, Y = -23.5445;
  vec3 p = P0 + X * E1 + Y * E2;
  vec3 a = yocto::normalize(p);

  double box_delta = 234013.0 / 1000000000.0;

  double best_dot = -1.0;
  int best_m1 = -1, best_m2 = -1;
  Tube229::AuditedAxis best_ax;

  for (int m1 = 500; m1 <= 1000; m1 += 25) {
    for (int m2 = 0; m2 <= 500; m2 += 25) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      std::string err;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) {
          vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                    ctr.y.ToDouble() / cert.B.ToDouble(),
                    ctr.z.ToDouble() / cert.B.ToDouble()};
          double d = yocto::dot(a, v);
          if (d > best_dot) {
            best_dot = d;
            best_m1 = m1;
            best_m2 = m2;
            best_ax = {cert, ctr, del};
          }
        }
      }
    }
  }

  std::cout << "Best tuned axis: m1=" << best_m1 << ", m2=" << best_m2
            << ", dot=" << best_dot
            << ", delta=" << best_ax.delta.ToString() << " (" << best_ax.delta.ToDouble() << ")\n";
  std::cout << "B=" << best_ax.cert.B.ToString() << "\n";
  std::cout << "Center: (" << best_ax.center.x.ToString() << ", "
            << best_ax.center.y.ToString() << ", "
            << best_ax.center.z.ToString() << ")\n";

  return 0;
}
