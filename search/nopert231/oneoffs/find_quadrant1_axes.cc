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
  double norm_u0_sq = yocto::dot(u0, u0);
  double norm_u0 = std::sqrt(norm_u0_sq);
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double box_delta = 234013.0 / 1000000000.0;

  // Let's test adversary directions in the uncovered region:
  // x in [0.3, 0.8], y in [0.3, 0.8]
  std::vector<vec3> adv_dirs;
  for (double x = 0.3; x <= 0.8; x += 0.1) {
    for (double y = 0.3; y <= 0.8; y += 0.1) {
      if (x * x + y * y >= 1.0) continue;
      double z = std::sqrt(1.0 - x * x - y * y);
      vec3 a = x * k1 + y * k2 + z * e3;
      adv_dirs.push_back(a);
    }
  }

  // Generate axes on Triples:
  // Triples that have support on faces:
  // e.g. {1, 4, ...}, {2, 10, ...}, {3, 2, ...}, {10, 15, ...}, {13, 14, ...}, {15, 19, ...}
  struct TripleSpec {
    int s1, f1, s2, f2, v1;
    int s3, f3, s4, f4, v2;
    int s5, f5, s6, f6, v3;
  };

  std::vector<TripleSpec> specs = {
    {2, 10, 10, 2, 10,  1, 15, 15, 1, 15,  4, 19, 19, 4, 19},
    {2, 10, 10, 3, 10,  1, 15, 15, 2, 15,  4, 19, 19, 1, 19},
    {2, 1, 1, 15, 1,    1, 4, 4, 19, 4,    4, 8, 8, 3, 8},
    {3, 2, 2, 1, 2,     4, 8, 8, 9, 8,     15, 19, 19, 3, 19},
    {1, 4, 4, 8, 4,     13, 14, 14, 15, 14, 3, 2, 2, 1, 2},
    {2, 1, 1, 4, 1,     10, 15, 15, 19, 15, 3, 2, 2, 1, 2},
    {4, 8, 8, 9, 8,     10, 15, 15, 19, 15, 2, 1, 1, 4, 1},
    {13, 14, 14, 15, 14, 4, 8, 8, 9, 8,   2, 1, 1, 4, 1},
    {1, 15, 15, 2, 15,  3, 2, 2, 1, 2,     4, 8, 8, 9, 8}
  };

  for (const auto &sp : specs) {
    for (int m1 = 0; m1 <= 1000; m1 += 100) {
      for (int m2 = 0; m2 <= 1000; m2 += 100) {
        for (int m3 = 0; m3 <= 1000; m3 += 100) {
          ContactInfo contacts[3] = {
            {sp.s1, sp.f1, sp.s2, sp.f2, m1, sp.v1},
            {sp.s3, sp.f3, sp.s4, sp.f4, m2, sp.v2},
            {sp.s5, sp.f5, sp.s6, sp.f6, m3, sp.v3}
          };
          AxisCertificate ax_cert;
          BigVecQ3 center;
          BigRat delta;
          if (Tube229::AuditAxis(tri, contacts, &ax_cert, &center, &delta, &err, BigRat(0))) {
            if (delta.ToDouble() <= box_delta) {
              double B = ax_cert.B.ToDouble();
              vec3 v = {center.x.ToDouble() / B, center.y.ToDouble() / B, center.z.ToDouble() / B};
              double c0 = yocto::dot(v, u0) / norm_u0_sq;
              if (c0 >= 0) {
                double c1 = yocto::dot(v, k1);
                double c2 = yocto::dot(v, k2);
                if (c1 > 0 && c2 > 0) {
                  std::cout << "Found promising axis: c0=" << c0 << ", c1=" << c1 << ", c2=" << c2
                            << ", delta=" << delta.ToDouble() << "\n";
                  std::cout << "  Triple: " << sp.s1 << "->" << sp.f1 << ", mix=("
                            << m1 << "," << m2 << "," << m3 << ")\n";
                  return 0;
                }
              }
            }
          }
        }
      }
    }
  }

  std::cout << "None found in initial sweep.\n";
  return 0;
}
