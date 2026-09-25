#include <iostream>
#include <vector>
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
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  // Fixed axes 1 and 3:
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 500, 1),
    MakeContact(10, 15, 15, 19, 666, 15),
    MakeContact(3, 2, 2, 1, 0, 2)
  };
  AxisCertificate ax1;
  BigVecQ3 ctr1;
  BigRat del1;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  vec3 u1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(),
             ctr1.y.ToDouble() / ax1.B.ToDouble(),
             ctr1.z.ToDouble() / ax1.B.ToDouble()};

  ContactInfo c3[3] = {
    MakeContact(2, 1, 1, 4, 333, 1),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  AxisCertificate ax3;
  BigVecQ3 ctr3;
  BigRat del3;
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));
  vec3 u3 = {ctr3.x.ToDouble() / ax3.B.ToDouble(),
             ctr3.y.ToDouble() / ax3.B.ToDouble(),
             ctr3.z.ToDouble() / ax3.B.ToDouble()};

  double delta = 0.000117006;
  double c_cone = 0.028;
  double box_c = 0.0001;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  double best_min_l = -1;
  int best_m0 = -1, best_m1 = -1, best_m2 = -1;

  for (int m0 = 100; m0 <= 900; m0 += 50) {
    for (int m1 = 100; m1 <= 900; m1 += 50) {
      for (int m2 = 100; m2 <= 900; m2 += 50) {
        ContactInfo c2[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(8, 9, 9, 10, m1, 9),
          MakeContact(3, 2, 2, 1, m2, 2)
        };
        AxisCertificate ax2;
        BigVecQ3 ctr2;
        BigRat del2;
        if (!Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0))) continue;
        vec3 u2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(),
                   ctr2.y.ToDouble() / ax2.B.ToDouble(),
                   ctr2.z.ToDouble() / ax2.B.ToDouble()};

        vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
        double det = yocto::dot(d1, yocto::cross(d2, d3));
        if (std::abs(det) < 1e-8) continue;
        vec3 c23 = yocto::cross(d2, d3);

        double min_l = 1e9;
        for (const auto &p : oct) {
          vec3 dp = p - v0;
          double l1 = yocto::dot(dp, c23) / det;
          double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
          double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
          double l0 = 1.0 - l1 - l2 - l3;
          min_l = std::min({min_l, l0, l1, l2, l3});
        }

        if (min_l > best_min_l) {
          best_min_l = min_l;
          best_m0 = m0; best_m1 = m1; best_m2 = m2;
          if (best_min_l > 0) {
            std::cout << "SUCCESS! min_l = " << best_min_l
                      << " with mixes (" << m0 << ", " << m1 << ", " << m2 << ")\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Best min_l: " << best_min_l << " with mixes ("
            << best_m0 << ", " << best_m1 << ", " << best_m2 << ")\n";
  return 0;
}
