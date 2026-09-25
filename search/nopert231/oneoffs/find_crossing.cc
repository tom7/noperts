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

static bool SolveTetraOrigin(const BigVecQ3& p0, const BigVecQ3& p1,
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);
  std::string err;

  std::cout << "Testing variations around the crossing...\n";

  for (int m0_0 = 400; m0_0 <= 1000; m0_0 += 100) {
    for (int m0 = 385; m0 <= 395; m0++) {
      ContactInfo c0[3] = {
        MakeContact(3, 2, 2, 1, m0_0, 2),
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(14, 15, 15, 19, m0, 15)
      };
      AxisCertificate ax0; BigVecQ3 cnt0; BigRat del0;
      if (!Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0))) continue;
      BigVecQ3 u0 = cnt0 / ax0.B;

      for (int m1_0 : {0, 20, 50, 100, 200}) {
        for (int m1_1 : {650, 700, 750}) {
          ContactInfo c1[3] = {
            MakeContact(2, 1, 1, 4, m1_0, 1),
            MakeContact(10, 15, 15, 19, m1_1, 15),
            MakeContact(19, 3, 3, 2, 750, 3)
          };
          AxisCertificate ax1; BigVecQ3 cnt1; BigRat del1;
          if (!Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &del1, &err, BigRat(0))) continue;
          BigVecQ3 u1 = cnt1 / ax1.B;

          for (int m2_0 : {800, 900, 1000}) {
            for (int m2_1 : {650, 700, 750}) {
              ContactInfo c2[3] = {
                MakeContact(2, 1, 1, 4, m2_0, 1),
                MakeContact(8, 9, 9, 10, m2_1, 9),
                MakeContact(9, 10, 10, 15, 900, 10)
              };
              AxisCertificate ax2; BigVecQ3 cnt2; BigRat del2;
              if (!Tube229::AuditAxis(tri, c2, &ax2, &cnt2, &del2, &err, BigRat(0))) continue;
              BigVecQ3 u2 = cnt2 / ax2.B;

              for (int m3_0 : {0, 20, 50, 80}) {
                for (int m3_1 : {450, 500, 550}) {
                  for (int m3_2 : {30, 40, 50, 60, 70}) {
                    ContactInfo c3[3] = {
                      MakeContact(3, 2, 2, 1, m3_0, 2),
                      MakeContact(1, 4, 4, 8, m3_1, 4),
                      MakeContact(10, 15, 15, 19, m3_2, 15)
                    };
                    AxisCertificate ax3; BigVecQ3 cnt3; BigRat del3;
                    if (!Tube229::AuditAxis(tri, c3, &ax3, &cnt3, &del3, &err, BigRat(0))) continue;
                    BigVecQ3 u3 = cnt3 / ax3.B;

              BigRat w[4];
              if (SolveTetraOrigin(u0, u1, u2, u3, w)) {
                double min_w = std::min({w[0].ToDouble(), w[1].ToDouble(), w[2].ToDouble(), w[3].ToDouble()});
                static double best_min_w = -1.0;
                if (min_w > best_min_w) {
                  best_min_w = min_w;
                  std::cout << "New best min_w: " << best_min_w << " (w0=" << w[0].ToDouble()
                            << ", w1=" << w[1].ToDouble() << ", w2=" << w[2].ToDouble()
                            << ", w3=" << w[3].ToDouble() << ")\n";
                }
                if (w[0] > BigRat(0) && w[1] > BigRat(0) && w[2] > BigRat(0) && w[3] > BigRat(0)) {
                  std::cout << "SUCCESS! ALL 4 WEIGHTS ARE STRICTLY POSITIVE!\n";
                  std::cout << "  m0_0=" << m0_0 << " m0=" << m0 << "\n";
                  std::cout << "  m1_0=" << m1_0 << "\n";
                  std::cout << "  m2_0=" << m2_0 << "\n";
                  std::cout << "  m3_0=" << m3_0 << " m3_2=" << m3_2 << "\n";
                  std::cout << "  weights: " << w[0].ToDouble() << ", " << w[1].ToDouble() << ", "
                            << w[2].ToDouble() << ", " << w[3].ToDouble() << "\n";
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
  }

  std::cout << "Done testing variations.\n";
  return 0;
}
