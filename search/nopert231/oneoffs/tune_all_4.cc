#include <iostream>
#include <vector>
#include <iomanip>
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

static bool SolveTetraPoint(const vec3& p0, const vec3& p1,
                            const vec3& p2, const vec3& p3,
                            const vec3& target,
                            double w[4]) {
  double M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  double rhs[3] = {target.x - p3.x, target.y - p3.y, target.z - p3.z};

  double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (std::abs(det) < 1e-12) return false;

  double d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  double d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  double d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = 1.0 - w[0] - w[1] - w[2];
  return true;
}

struct AxisCand {
  ContactInfo c[3];
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  vec3 u;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  std::cout << "Precomputing candidate variations for Axes 0, 1, 2, 3...\n";

  // Axis 0 variations:
  std::vector<AxisCand> list0;
  for (int m0_0 : {100, 150, 200, 250, 300, 350}) {
    for (int m0_2 : {380, 385, 390, 395, 400, 405, 410}) {
      ContactInfo c0[3] = {
        MakeContact(3, 2, 2, 1, m0_0, 2),
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(14, 15, 15, 19, m0_2, 15)
      };
      AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
      if (Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0))) {
        vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
                   ctr0.y.ToDouble() / ax0.B.ToDouble(),
                   ctr0.z.ToDouble() / ax0.B.ToDouble()};
        list0.push_back({{c0[0], c0[1], c0[2]}, ax0, ctr0, del0, u0});
      }
    }
  }
  std::cout << "Axis 0 candidates: " << list0.size() << "\n";

  // Axis 1 variations (1283 base):
  std::vector<AxisCand> list1;
  for (int m1_0 : {350, 400, 450, 500, 600}) {
    for (int m1_1 : {550, 600, 650, 666, 700, 750}) {
      for (int m1_2 : {0, 50, 100}) {
        ContactInfo c1[3] = {
          MakeContact(2, 1, 1, 4, m1_0, 1),
          MakeContact(10, 15, 15, 19, m1_1, 15),
          MakeContact(3, 2, 2, 1, m1_2, 2)
        };
        AxisCertificate ax1; BigVecQ3 ctr1; BigRat del1;
        if (Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0))) {
          vec3 u1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(),
                     ctr1.y.ToDouble() / ax1.B.ToDouble(),
                     ctr1.z.ToDouble() / ax1.B.ToDouble()};
          list1.push_back({{c1[0], c1[1], c1[2]}, ax1, ctr1, del1, u1});
        }
      }
    }
  }
  std::cout << "Axis 1 candidates: " << list1.size() << "\n";

  // Axis 2 variations (4074 base):
  std::vector<AxisCand> list2;
  for (int m2_0 : {500, 600, 700, 800, 900}) {
    for (int m2_1 : {150, 200, 250, 300}) {
      for (int m2_2 : {450, 500, 550, 600, 666}) {
        ContactInfo c2[3] = {
          MakeContact(3, 2, 2, 1, m2_0, 2),
          MakeContact(8, 9, 9, 10, m2_1, 9),
          MakeContact(3, 2, 2, 1, m2_2, 2)
        };
        AxisCertificate ax2; BigVecQ3 ctr2; BigRat del2;
        if (Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0))) {
          vec3 u2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(),
                     ctr2.y.ToDouble() / ax2.B.ToDouble(),
                     ctr2.z.ToDouble() / ax2.B.ToDouble()};
          list2.push_back({{c2[0], c2[1], c2[2]}, ax2, ctr2, del2, u2});
        }
      }
    }
  }
  std::cout << "Axis 2 candidates: " << list2.size() << "\n";

  // Axis 3 variations (1041 base):
  std::vector<AxisCand> list3;
  for (int m3_0 : {200, 250, 300, 333, 400}) {
    for (int m3_1 : {500, 600, 700, 800}) {
      for (int m3_2 : {200, 250, 300, 350, 400, 450}) {
        ContactInfo c3[3] = {
          MakeContact(2, 1, 1, 4, m3_0, 1),
          MakeContact(1, 4, 4, 8, m3_1, 4),
          MakeContact(10, 15, 15, 19, m3_2, 15)
        };
        AxisCertificate ax3; BigVecQ3 ctr3; BigRat del3;
        if (Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0))) {
          vec3 u3 = {ctr3.x.ToDouble() / ax3.B.ToDouble(),
                     ctr3.y.ToDouble() / ax3.B.ToDouble(),
                     ctr3.z.ToDouble() / ax3.B.ToDouble()};
          list3.push_back({{c3[0], c3[1], c3[2]}, ax3, ctr3, del3, u3});
        }
      }
    }
  }
  std::cout << "Axis 3 candidates: " << list3.size() << "\n";

  double c_val = 0.00041;
  double delta_val = 0.00024;
  double R = 1.75 * (c_val + delta_val);
  vec3 oct[6] = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::cout << "Optimizing quad cage across all candidate combinations...\n";
  double best_min_w = -1.0;
  size_t best_i0 = 0, best_i1 = 0, best_i2 = 0, best_i3 = 0;
  double best_c_cone = 0.025;

  for (double c_cone : {0.022, 0.025, 0.028, 0.030}) {
    double scale = (c_val + delta_val) / c_cone;

    // Greedy hill climber initialized at best known indices:
    size_t cur0 = 0, cur1 = 0, cur2 = 0, cur3 = 0;

    auto eval = [&](size_t i0, size_t i1, size_t i2, size_t i3) -> double {
      vec3 p0 = list0[i0].u * scale;
      const vec3& p1 = list1[i1].u;
      const vec3& p2 = list2[i2].u;
      const vec3& p3 = list3[i3].u;

      double min_w_tetra = 1.0;
      for (int k = 0; k < 6; k++) {
        double w[4];
        if (!SolveTetraPoint(p0, p1, p2, p3, oct[k], w)) return -1.0;
        double min_w = std::min({w[0], w[1], w[2], w[3]});
        if (min_w < min_w_tetra) min_w_tetra = min_w;
      }
      return min_w_tetra;
    };

    // Coordinate ascent passes:
    double cur_score = eval(cur0, cur1, cur2, cur3);
    bool improved = true;
    while (improved) {
      improved = false;

      // Optimize axis 0:
      for (size_t i0 = 0; i0 < list0.size(); i0++) {
        double sc = eval(i0, cur1, cur2, cur3);
        if (sc > cur_score) { cur_score = sc; cur0 = i0; improved = true; }
      }
      // Optimize axis 1:
      for (size_t i1 = 0; i1 < list1.size(); i1++) {
        double sc = eval(cur0, i1, cur2, cur3);
        if (sc > cur_score) { cur_score = sc; cur1 = i1; improved = true; }
      }
      // Optimize axis 2:
      for (size_t i2 = 0; i2 < list2.size(); i2++) {
        double sc = eval(cur0, cur1, i2, cur3);
        if (sc > cur_score) { cur_score = sc; cur2 = i2; improved = true; }
      }
      // Optimize axis 3:
      for (size_t i3 = 0; i3 < list3.size(); i3++) {
        double sc = eval(cur0, cur1, cur2, i3);
        if (sc > cur_score) { cur_score = sc; cur3 = i3; improved = true; }
      }
    }

    std::cout << "c_cone = " << c_cone << " -> score = " << cur_score << "\n";
    if (cur_score > best_min_w) {
      best_min_w = cur_score;
      best_i0 = cur0; best_i1 = cur1; best_i2 = cur2; best_i3 = cur3;
      best_c_cone = c_cone;
    }
  }

  std::cout << "\n============================================\n";
  std::cout << "OPTIMIZATION COMPLETE: Best min_w = " << best_min_w << " at c_cone = " << best_c_cone << "\n";
  std::cout << "============================================\n";

  return 0;
}
