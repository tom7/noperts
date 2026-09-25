#include <iostream>
#include <vector>
#include <iomanip>
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

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Zero-defect Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  if (!Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0))) {
    std::cout << "Axis 0 audit failed: " << err << "\n";
    return 1;
  }
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  double c_cone = 0.025;
  double c_val = 0.00041;
  double delta_val = 0.00024;
  double scale = (c_val + delta_val) / c_cone;
  vec3 p0 = u0 * scale; // Note: NOT normalized, exactly u0 * scale as in Lean!
  double R = 1.75 * (c_val + delta_val);

  vec3 oct[6] = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::cout << "Searching mix variations of 1283, 4074, 1041...\n";
  double best_min_w = -1.0;

  for (int m1_0 : {400, 500, 600}) {
    for (int m1_1 : {600, 666, 700}) {
      ContactInfo c1[3] = {
        MakeContact(2, 1, 1, 4, m1_0, 1),
        MakeContact(10, 15, 15, 19, m1_1, 15),
        MakeContact(3, 2, 2, 1, 0, 2)
      };
      AxisCertificate ax1; BigVecQ3 ctr1; BigRat del1;
      if (!Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0))) continue;
      vec3 p1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(),
                 ctr1.y.ToDouble() / ax1.B.ToDouble(),
                 ctr1.z.ToDouble() / ax1.B.ToDouble()};

      for (int m2_1 : {100, 150, 200, 250}) {
        for (int m2_0 : {600, 700, 800, 900, 1000}) {
          for (int m2_2 : {500, 600, 666, 700}) {
            ContactInfo c2[3] = {
              MakeContact(3, 2, 2, 1, m2_0, 2),
              MakeContact(8, 9, 9, 10, m2_1, 9),
              MakeContact(3, 2, 2, 1, m2_2, 2)
            };
            AxisCertificate ax2; BigVecQ3 ctr2; BigRat del2;
            if (!Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0))) continue;
            vec3 p2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(),
                       ctr2.y.ToDouble() / ax2.B.ToDouble(),
                       ctr2.z.ToDouble() / ax2.B.ToDouble()};

            for (int m3_0 : {250, 333, 400}) {
              for (int m3_1 : {600, 700, 800}) {
                for (int m3_2 = 250; m3_2 <= 800; m3_2 += 50) {
                  ContactInfo c3[3] = {
                    MakeContact(2, 1, 1, 4, m3_0, 1),
                    MakeContact(1, 4, 4, 8, m3_1, 4),
                    MakeContact(10, 15, 15, 19, m3_2, 15)
                  };
                  AxisCertificate ax3; BigVecQ3 ctr3; BigRat del3;
                  if (!Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0))) continue;
                  vec3 p3 = {ctr3.x.ToDouble() / ax3.B.ToDouble(),
                             ctr3.y.ToDouble() / ax3.B.ToDouble(),
                             ctr3.z.ToDouble() / ax3.B.ToDouble()};

                  bool all_pos = true;
                  double min_w_tetra = 1.0;
                  for (int k = 0; k < 6; k++) {
                    double w[4];
                    if (!SolveTetraPoint(p0, p1, p2, p3, oct[k], w)) {
                      all_pos = false; break;
                    }
                    double min_w = std::min({w[0], w[1], w[2], w[3]});
                    if (min_w < min_w_tetra) min_w_tetra = min_w;
                    if (min_w <= 0.0) {
                      all_pos = false; break;
                    }
                  }

                  if (min_w_tetra > best_min_w) {
                    best_min_w = min_w_tetra;
                    std::cout << "New best min_w: " << best_min_w << "\n";
                    std::cout << "  m1={" << m1_0 << "," << m1_1 << "} "
                              << "m2={" << m2_0 << "," << m2_1 << "," << m2_2 << "} "
                              << "m3={" << m3_0 << "," << m3_1 << "," << m3_2 << "}\n";
                    if (best_min_w > 0.0) {
                      std::cout << "SUCCESS! CAGE COVERS ALL 6 OCTAHEDRON VERTICES!\n";
                      return 0;
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  std::cout << "Search complete. Best min_w: " << best_min_w << "\n";
  return 0;
}
