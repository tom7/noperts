#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
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

  // Axis 64:
  //   v=1 mix=200 e1=18->1 e2=1->5
  //   v=10 mix=200 e1=9->10 e2=10->15
  //   v=15 mix=200 e1=10->15 e2=15->19
  // Axis 77:
  //   v=19 mix=200 e1=15->19 e2=19->3
  //   v=8 mix=600 e1=5->8 e2=8->9
  //   v=19 mix=600 e1=15->19 e2=19->3
  // Axis 266:
  //   v=2 mix=200 e1=3->2 e2=2->1
  //   v=1 mix=400 e1=2->1 e2=1->5
  //   v=15 mix=800 e1=14->15 e2=15->19

  ContactInfo a1[3] = {
    MakeContact(18, 1, 1, 5, 200, 1),
    MakeContact(9, 10, 10, 15, 200, 10),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo a2[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(5, 8, 8, 9, 600, 8),
    MakeContact(15, 19, 19, 3, 600, 19)
  };
  ContactInfo a3[3] = {
    MakeContact(3, 2, 2, 1, 200, 2),
    MakeContact(2, 1, 1, 5, 400, 1),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  double delta = 3.33e-7;
  double box_c = 1e-7;
  double c_cone = 0.028;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct_dirs = {
    {1, 0, 0}, {-1, 0, 0},
    {0, 1, 0}, {0, -1, 0},
    {0, 0, 1}, {0, 0, -1}
  };

  auto EvalMinL = [&](const vec3 &u1, const vec3 &u2, const vec3 &u3) -> double {
    vec3 d1 = u1 - v0, d2 = u2 - v0, d3 = u3 - v0;
    vec3 c12 = yocto::cross(d1, d2);
    vec3 c23 = yocto::cross(d2, d3);
    vec3 c31 = yocto::cross(d3, d1);
    double det = yocto::dot(c12, d3);
    if (std::abs(det) < 1e-8) return -1e9;

    double min_l = 1e9;
    for (int m = 0; m < 6; m++) {
      vec3 dp = oct_dirs[m] * R - v0;
      double l1 = yocto::dot(dp, c23) / det;
      double l2 = yocto::dot(dp, c31) / det;
      double l3 = yocto::dot(dp, c12) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      double min_vert = std::min({l0, l1, l2, l3});
      if (min_vert < min_l) min_l = min_vert;
    }
    return min_l;
  };

  // Base u1, u2, u3:
  AxisCertificate cert1, cert2, cert3;
  BigVecQ3 ctr1, ctr2, ctr3;
  BigRat del1, del2, del3;
  Tube229::AuditAxis(tri, a1, &cert1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, a2, &cert2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, a3, &cert3, &ctr3, &del3, &err, BigRat(0));

  vec3 u1 = {ctr1.x.ToDouble() / cert1.B.ToDouble(), ctr1.y.ToDouble() / cert1.B.ToDouble(), ctr1.z.ToDouble() / cert1.B.ToDouble()};
  vec3 u2 = {ctr2.x.ToDouble() / cert2.B.ToDouble(), ctr2.y.ToDouble() / cert2.B.ToDouble(), ctr2.z.ToDouble() / cert2.B.ToDouble()};
  vec3 u3 = {ctr3.x.ToDouble() / cert3.B.ToDouble(), ctr3.y.ToDouble() / cert3.B.ToDouble(), ctr3.z.ToDouble() / cert3.B.ToDouble()};

  std::cout << "Base min_l = " << EvalMinL(u1, u2, u3) << "\n";

  // Grid search fine mixes around a1, a2, a3:
  double best_l = EvalMinL(u1, u2, u3);
  int best_m[3][3] = {
    {200, 200, 200},
    {200, 600, 600},
    {200, 400, 800}
  };

  // Try varying each mix by -100 to +100 in steps of 20
  for (int step = 0; step < 5; step++) {
    bool improved = false;
    for (int ax = 0; ax < 3; ax++) {
      for (int c = 0; c < 3; c++) {
        int orig_m = best_m[ax][c];
        for (int dm = -50; dm <= 50; dm += 10) {
          if (dm == 0) continue;
          int new_m = orig_m + dm;
          if (new_m <= 0 || new_m >= 1000) continue;

          ContactInfo test_c[3];
          for (int k = 0; k < 3; k++) {
            if (ax == 0) test_c[k] = a1[k];
            else if (ax == 1) test_c[k] = a2[k];
            else test_c[k] = a3[k];
            test_c[k].mix = best_m[ax][k];
          }
          test_c[c].mix = new_m;

          AxisCertificate tc;
          BigVecQ3 tctr;
          BigRat tdel;
          if (!Tube229::AuditAxis(tri, test_c, &tc, &tctr, &tdel, &err, BigRat(0))) continue;

          vec3 tu = {tctr.x.ToDouble() / tc.B.ToDouble(), tctr.y.ToDouble() / tc.B.ToDouble(), tctr.z.ToDouble() / tc.B.ToDouble()};
          vec3 tu1 = (ax == 0) ? tu : u1;
          vec3 tu2 = (ax == 1) ? tu : u2;
          vec3 tu3 = (ax == 2) ? tu : u3;

          double l = EvalMinL(tu1, tu2, tu3);
          if (l > best_l) {
            best_l = l;
            best_m[ax][c] = new_m;
            if (ax == 0) u1 = tu;
            else if (ax == 1) u2 = tu;
            else u3 = tu;
            improved = true;
            std::cout << "Improved to " << best_l << " (ax=" << ax << ", c=" << c << ", mix=" << new_m << ")\n";
            if (best_l > 0) {
              std::cout << "SUCCESS! Strict positive cage achieved!\n";
              return 0;
            }
          }
        }
      }
    }
    if (!improved) break;
  }

  std::cout << "Final best_l = " << best_l << "\n";
  return 0;
}
