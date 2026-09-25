#include <iostream>
#include <iomanip>
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

struct PreAxis {
  ContactInfo c[3];
  AxisCertificate ax;
  BigVecQ3 cnt;
  BigVecQ3 u_ex;
  vec3 u;
};

static inline bool SolveTetraOriginDouble(const vec3& p0, const vec3& p1,
                                         const vec3& p2, const vec3& p3,
                                         double w[4]) {
  double M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  double rhs[3] = {-p3.x, -p3.y, -p3.z};

  double det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (std::abs(det) < 1e-12) return false;

  double inv_det = 1.0 / det;
  double d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  double d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  double d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 * inv_det;
  w[1] = d1 * inv_det;
  w[2] = d2 * inv_det;
  w[3] = 1.0 - w[0] - w[1] - w[2];
  return true;
}

static bool SolveTetraOriginBig(const BigVecQ3& p0, const BigVecQ3& p1,
                                const BigVecQ3& p2, const BigVecQ3& p3,
                                BigRat w[4]) {
  BigRat M[3][3] = {
    {p0.x - p3.x, p1.x - p3.x, p2.x - p3.x},
    {p0.y - p3.y, p1.y - p3.y, p2.y - p3.y},
    {p0.z - p3.z, p1.z - p3.z, p2.z - p3.z}
  };
  BigRat rhs[3] = {-p3.x, -p3.y, -p3.z};

  BigRat det = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
               M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
               M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  if (det == BigRat(0)) return false;

  BigRat d0 = rhs[0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
              M[0][1] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) +
              M[0][2] * (rhs[1] * M[2][1] - M[1][1] * rhs[2]);

  BigRat d1 = M[0][0] * (rhs[1] * M[2][2] - M[1][2] * rhs[2]) -
              rhs[0] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
              M[0][2] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]);

  BigRat d2 = M[0][0] * (M[1][1] * rhs[2] - rhs[1] * M[2][1]) -
              M[0][1] * (M[1][0] * rhs[2] - rhs[1] * M[2][0]) +
              rhs[0] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);

  w[0] = d0 / det;
  w[1] = d1 / det;
  w[2] = d2 / det;
  w[3] = BigRat(1) - w[0] - w[1] - w[2];
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  std::cout << "Precomputing candidate sets...\n";

  // Precompute set 0:
  std::vector<PreAxis> set0;
  for (int m0_0 : {280, 320, 360, 400}) {
    for (int m0_2 = 360; m0_2 <= 440; m0_2 += 5) {
      ContactInfo c[3] = {
        MakeContact(3, 2, 2, 1, m0_0, 2),
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(14, 15, 15, 19, m0_2, 15)
      };
      AxisCertificate ax; BigVecQ3 cnt; BigRat del;
      if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
        BigVecQ3 u_ex = cnt / ax.B;
        vec3 u = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
        set0.push_back({ {c[0], c[1], c[2]}, ax, cnt, u_ex, u });
      }
    }
  }
  std::cout << "Set 0 size: " << set0.size() << "\n";

  // Precompute set 1:
  std::vector<PreAxis> set1;
  for (int m1_0 : {0, 10, 20}) {
    for (int m1_1 = 660; m1_1 <= 740; m1_1 += 10) {
      for (int m1_2 : {720, 750, 780}) {
        ContactInfo c[3] = {
          MakeContact(2, 1, 1, 4, m1_0, 1),
          MakeContact(10, 15, 15, 19, m1_1, 15),
          MakeContact(19, 3, 3, 2, m1_2, 3)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          BigVecQ3 u_ex = cnt / ax.B;
          vec3 u = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
          set1.push_back({ {c[0], c[1], c[2]}, ax, cnt, u_ex, u });
        }
      }
    }
  }
  std::cout << "Set 1 size: " << set1.size() << "\n";

  // Precompute set 2 (both contact triples):
  std::vector<PreAxis> set2;
  // Triple A: {2, 1, 1, 0}, {10, 15, 15, 19}, {10, 15, 15, 19}
  for (int m2_0 = 100; m2_0 <= 300; m2_0 += 20) {
    for (int m2_1 = 700; m2_1 <= 900; m2_1 += 20) {
      for (int m2_2 = 100; m2_2 <= 300; m2_2 += 20) {
        ContactInfo c[3] = {
          MakeContact(2, 1, 1, 0, m2_0, 1),
          MakeContact(10, 15, 15, 19, m2_1, 15),
          MakeContact(10, 15, 15, 19, m2_2, 15)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          BigVecQ3 u_ex = cnt / ax.B;
          vec3 u = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
          set2.push_back({ {c[0], c[1], c[2]}, ax, cnt, u_ex, u });
        }
      }
    }
  }
  // Triple B: {19, 3, 3, 2}, {2, 1, 1, 0}, {10, 15, 15, 19}
  for (int m2_0 = 10; m2_0 <= 90; m2_0 += 20) {
    for (int m2_2 = 390; m2_2 <= 470; m2_2 += 20) {
      ContactInfo c[3] = {
        MakeContact(19, 3, 3, 2, m2_0, 3),
        MakeContact(2, 1, 1, 0, 200, 1),
        MakeContact(10, 15, 15, 19, m2_2, 15)
      };
      AxisCertificate ax; BigVecQ3 cnt; BigRat del;
      if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
        BigVecQ3 u_ex = cnt / ax.B;
        vec3 u = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
        set2.push_back({ {c[0], c[1], c[2]}, ax, cnt, u_ex, u });
      }
    }
  }
  std::cout << "Set 2 size: " << set2.size() << "\n";

  // Precompute set 3 (both contact triples):
  std::vector<PreAxis> set3;
  // Triple A: {3, 2, 2, 1}, {8, 9, 9, 10}, {3, 2, 2, 1}
  for (int m3_0 = 300; m3_0 <= 600; m3_0 += 30) {
    for (int m3_1 = 150; m3_1 <= 250; m3_1 += 20) {
      for (int m3_2 = 500; m3_2 <= 700; m3_2 += 30) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m3_0, 2),
          MakeContact(8, 9, 9, 10, m3_1, 9),
          MakeContact(3, 2, 2, 1, m3_2, 2)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          BigVecQ3 u_ex = cnt / ax.B;
          vec3 u = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
          set3.push_back({ {c[0], c[1], c[2]}, ax, cnt, u_ex, u });
        }
      }
    }
  }
  // Triple B: {3, 2, 2, 1}, {8, 9, 9, 10}, {9, 10, 10, 13}
  for (int m3_0 = 300; m3_0 <= 450; m3_0 += 30) {
    for (int m3_1 = 150; m3_1 <= 250; m3_1 += 20) {
      for (int m3_2 = 10; m3_2 <= 90; m3_2 += 20) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m3_0, 2),
          MakeContact(8, 9, 9, 10, m3_1, 9),
          MakeContact(9, 10, 10, 13, m3_2, 10)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          BigVecQ3 u_ex = cnt / ax.B;
          vec3 u = {u_ex.x.ToDouble(), u_ex.y.ToDouble(), u_ex.z.ToDouble()};
          set3.push_back({ {c[0], c[1], c[2]}, ax, cnt, u_ex, u });
        }
      }
    }
  }
  std::cout << "Set 3 size: " << set3.size() << "\n";

  std::cout << "Searching combinations in double precision...\n";
  double best_min_w = -1e9;
  long long evals = 0;

  for (size_t i0 = 0; i0 < set0.size(); i0++) {
    const auto& a0 = set0[i0];
    for (size_t i1 = 0; i1 < set1.size(); i1++) {
      const auto& a1 = set1[i1];
      for (size_t i2 = 0; i2 < set2.size(); i2++) {
        const auto& a2 = set2[i2];
        for (size_t i3 = 0; i3 < set3.size(); i3++) {
          const auto& a3 = set3[i3];
          evals++;

          double w[4];
          if (!SolveTetraOriginDouble(a0.u, a1.u, a2.u, a3.u, w)) continue;

          double min_w = std::min({w[0], w[1], w[2], w[3]});
          if (min_w > best_min_w) {
            best_min_w = min_w;
            if (best_min_w > -1e-6) {
              std::cout << "New best min_w: " << best_min_w
                        << " (w0=" << w[0] << ", w1=" << w[1]
                        << ", w2=" << w[2] << ", w3=" << w[3] << ")\n";
              std::cout << "  i0=" << i0 << " i1=" << i1 << " i2=" << i2 << " i3=" << i3 << "\n";
              std::cout << "  c0 mix: " << a0.c[0].mix << ", " << a0.c[1].mix << ", " << a0.c[2].mix << "\n";
              std::cout << "  c1 mix: " << a1.c[0].mix << ", " << a1.c[1].mix << ", " << a1.c[2].mix << "\n";
              std::cout << "  c2 mix: " << a2.c[0].mix << ", " << a2.c[1].mix << ", " << a2.c[2].mix << "\n";
              std::cout << "  c3 mix: " << a3.c[0].mix << ", " << a3.c[1].mix << ", " << a3.c[2].mix << "\n";
            }

            if (min_w > 0.0) {
              std::cout << "\n============================================\n";
              std::cout << "VERIFYING IN BIGRAT RATIONAL ARITHMETIC!\n";
              BigRat bw[4];
              if (SolveTetraOriginBig(a0.u_ex, a1.u_ex, a2.u_ex, a3.u_ex, bw)) {
                std::cout << "Exact BigRat weights:\n";
                std::cout << "  w0 = " << bw[0].ToDouble() << "\n";
                std::cout << "  w1 = " << bw[1].ToDouble() << "\n";
                std::cout << "  w2 = " << bw[2].ToDouble() << "\n";
                std::cout << "  w3 = " << bw[3].ToDouble() << "\n";

                if (bw[0] > BigRat(0) && bw[1] > BigRat(0) &&
                    bw[2] > BigRat(0) && bw[3] > BigRat(0)) {
                  std::cout << "\nCONFIRMED! ALL 4 WEIGHTS STRICTLY POSITIVE IN RATIONALS!\n";
                  std::cout << "Axis 0:\n";
                  for (int c = 0; c < 3; c++) std::cout << "  {" << a0.c[c].edge_start << ", " << a0.c[c].edge_finish << ", " << a0.c[c].edge_start2 << ", " << a0.c[c].edge_finish2 << ", " << a0.c[c].mix << ", " << a0.c[c].vertex << "}\n";
                  std::cout << "Axis 1:\n";
                  for (int c = 0; c < 3; c++) std::cout << "  {" << a1.c[c].edge_start << ", " << a1.c[c].edge_finish << ", " << a1.c[c].edge_start2 << ", " << a1.c[c].edge_finish2 << ", " << a1.c[c].mix << ", " << a1.c[c].vertex << "}\n";
                  std::cout << "Axis 2:\n";
                  for (int c = 0; c < 3; c++) std::cout << "  {" << a2.c[c].edge_start << ", " << a2.c[c].edge_finish << ", " << a2.c[c].edge_start2 << ", " << a2.c[c].edge_finish2 << ", " << a2.c[c].mix << ", " << a2.c[c].vertex << "}\n";
                  std::cout << "Axis 3:\n";
                  for (int c = 0; c < 3; c++) std::cout << "  {" << a3.c[c].edge_start << ", " << a3.c[c].edge_finish << ", " << a3.c[c].edge_start2 << ", " << a3.c[c].edge_finish2 << ", " << a3.c[c].mix << ", " << a3.c[c].vertex << "}\n";
                  return 0;
                }
              }
            }
          }
        }
      }
    }
  }

  std::cout << "Done " << evals << " evaluations. Best min_w = " << best_min_w << "\n";
  return 0;
}
