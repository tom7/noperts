#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(1, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.001;
  double c_cone = 0.040;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;

  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  // Base contacts:
  // Axis 182:
  //   MakeContact(15, 19, 19, 3, 200, 19),
  //   MakeContact(5, 8, 8, 9, 600, 8),
  //   MakeContact(15, 19, 19, 3, 600, 19),
  // Axis 370:
  //   MakeContact(2, 1, 1, 4, 400, 1),
  //   MakeContact(9, 10, 10, 13, 200, 10),
  //   MakeContact(14, 15, 15, 19, 400, 15),
  // Axis 401:
  //   MakeContact(3, 2, 2, 1, 600, 2),
  //   MakeContact(2, 1, 1, 0, 200, 1),
  //   MakeContact(10, 15, 15, 19, 600, 15),

  std::vector<vec3> u1_cands, u2_cands, u3_cands;
  std::vector<ContactInfo[3]> c1_cands, c2_cands, c3_cands;

  for (int dm0 = -100; dm0 <= 100; dm0 += 50) {
    for (int dm1 = -100; dm1 <= 100; dm1 += 50) {
      for (int dm2 = -100; dm2 <= 100; dm2 += 50) {
        int m0 = 200 + dm0, m1 = 600 + dm1, m2 = 600 + dm2;
        if (m0 < 0 || m0 > 1000 || m1 < 0 || m1 > 1000 || m2 < 0 || m2 > 1000) continue;
        ContactInfo c[3] = {
          MakeContact(15, 19, 19, 3, m0, 19),
          MakeContact(5, 8, 8, 9, m1, 8),
          MakeContact(15, 19, 19, 3, m2, 19)
        };
        AxisCertificate cert; BigVecQ3 ctr; BigRat del;
        if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
          u1_cands.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                              ctr.y.ToDouble() / cert.B.ToDouble(),
                              ctr.z.ToDouble() / cert.B.ToDouble()});
        }
      }
    }
  }

  for (int dm0 = -100; dm0 <= 100; dm0 += 50) {
    for (int dm1 = -100; dm1 <= 100; dm1 += 50) {
      for (int dm2 = -100; dm2 <= 100; dm2 += 50) {
        int m0 = 400 + dm0, m1 = 200 + dm1, m2 = 400 + dm2;
        if (m0 < 0 || m0 > 1000 || m1 < 0 || m1 > 1000 || m2 < 0 || m2 > 1000) continue;
        ContactInfo c[3] = {
          MakeContact(2, 1, 1, 4, m0, 1),
          MakeContact(9, 10, 10, 13, m1, 10),
          MakeContact(14, 15, 15, 19, m2, 15)
        };
        AxisCertificate cert; BigVecQ3 ctr; BigRat del;
        if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
          u2_cands.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                              ctr.y.ToDouble() / cert.B.ToDouble(),
                              ctr.z.ToDouble() / cert.B.ToDouble()});
        }
      }
    }
  }

  for (int dm0 = -100; dm0 <= 100; dm0 += 50) {
    for (int dm1 = -100; dm1 <= 100; dm1 += 50) {
      for (int dm2 = -100; dm2 <= 100; dm2 += 50) {
        int m0 = 600 + dm0, m1 = 200 + dm1, m2 = 600 + dm2;
        if (m0 < 0 || m0 > 1000 || m1 < 0 || m1 > 1000 || m2 < 0 || m2 > 1000) continue;
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(2, 1, 1, 0, m1, 1),
          MakeContact(10, 15, 15, 19, m2, 15)
        };
        AxisCertificate cert; BigVecQ3 ctr; BigRat del;
        if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
          u3_cands.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                              ctr.y.ToDouble() / cert.B.ToDouble(),
                              ctr.z.ToDouble() / cert.B.ToDouble()});
        }
      }
    }
  }

  std::cout << "Candidates: u1=" << u1_cands.size() << ", u2=" << u2_cands.size() << ", u3=" << u3_cands.size() << "\n";

  double best_min_l = -1e9;
  for (const auto &v1 : u1_cands) {
    for (const auto &v2 : u2_cands) {
      for (const auto &v3 : u3_cands) {
        vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
        double det = yocto::dot(d1, yocto::cross(d2, d3));
        if (std::abs(det) < 1e-9) continue;
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
        }
      }
    }
  }

  std::cout << "Best min_l after mix tuning at c_cone = " << c_cone << ": " << best_min_l << "\n";
  return 0;
}
