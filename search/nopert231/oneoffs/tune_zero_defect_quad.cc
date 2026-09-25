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

struct AxisCand {
  int m[3];
  BigVecQ3 u;
  AxisCertificate ax;
  BigRat del;
};

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

  std::cout << "Precomputing zero-defect candidates for Axis 0...\n";
  std::vector<AxisCand> cands0;
  for (int m0 = 300; m0 <= 600; m0 += 50) {
    ContactInfo c[3] = {
      MakeContact(3, 2, 2, 1, 150, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(14, 15, 15, 19, m0, 15)
    };
    AxisCertificate ax; BigVecQ3 cnt; BigRat del;
    if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
      cands0.push_back({{150, 1000, m0}, cnt / ax.B, ax, del});
    }
  }
  std::cout << "Axis 0 candidates: " << cands0.size() << "\n";

  std::cout << "Precomputing zero-defect candidates for Axis 1...\n";
  std::vector<AxisCand> cands1;
  for (int m0 = 0; m0 <= 150; m0 += 50) {
    for (int m1 = 500; m1 <= 900; m1 += 100) {
      for (int m2 = 700; m2 <= 1000; m2 += 100) {
        ContactInfo c[3] = {
          MakeContact(2, 1, 1, 4, m0, 1),
          MakeContact(10, 15, 15, 19, m1, 15),
          MakeContact(19, 3, 3, 2, m2, 3)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          cands1.push_back({{m0, m1, m2}, cnt / ax.B, ax, del});
        }
      }
    }
  }
  std::cout << "Axis 1 candidates: " << cands1.size() << "\n";

  std::cout << "Precomputing zero-defect candidates for Axis 2...\n";
  std::vector<AxisCand> cands2;
  for (int m0 : {800, 900, 1000}) {
    for (int m1 : {800, 900, 1000}) {
      for (int m2 = 500; m2 <= 1000; m2 += 50) {
        ContactInfo c[3] = {
          MakeContact(2, 1, 1, 4, m0, 1),
          MakeContact(8, 9, 9, 10, m1, 9),
          MakeContact(9, 10, 10, 15, m2, 10)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          cands2.push_back({{m0, m1, m2}, cnt / ax.B, ax, del});
        }
      }
    }
  }
  std::cout << "Axis 2 candidates: " << cands2.size() << "\n";

  std::cout << "Precomputing zero-defect candidates for Axis 3...\n";
  std::vector<AxisCand> cands3;
  for (int m0 = 0; m0 <= 200; m0 += 50) {
    for (int m1 = 200; m1 <= 600; m1 += 100) {
      for (int m2 = 50; m2 <= 250; m2 += 50) {
        ContactInfo c[3] = {
          MakeContact(3, 2, 2, 1, m0, 2),
          MakeContact(1, 4, 4, 8, m1, 4),
          MakeContact(10, 15, 15, 19, m2, 15)
        };
        AxisCertificate ax; BigVecQ3 cnt; BigRat del;
        if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
          cands3.push_back({{m0, m1, m2}, cnt / ax.B, ax, del});
        }
      }
    }
  }
  std::cout << "Axis 3 candidates: " << cands3.size() << "\n";

  std::cout << "Searching combinations for origin containment...\n";
  double best_min_w = -1.0;
  for (const auto& a0 : cands0) {
    for (const auto& a1 : cands1) {
      for (const auto& a2 : cands2) {
        for (const auto& a3 : cands3) {
          BigRat w[4];
          if (SolveTetraOrigin(a0.u, a1.u, a2.u, a3.u, w)) {
            double min_w = std::min({w[0].ToDouble(), w[1].ToDouble(), w[2].ToDouble(), w[3].ToDouble()});
            if (min_w > best_min_w) {
              best_min_w = min_w;
              std::cout << "New best min weight: " << min_w << " (w0=" << w[0].ToDouble()
                        << " w1=" << w[1].ToDouble() << " w2=" << w[2].ToDouble()
                        << " w3=" << w[3].ToDouble() << ")\n";
              std::cout << "  ax0: {" << a0.m[0] << "," << a0.m[1] << "," << a0.m[2] << "}\n";
              std::cout << "  ax1: {" << a1.m[0] << "," << a1.m[1] << "," << a1.m[2] << "}\n";
              std::cout << "  ax2: {" << a2.m[0] << "," << a2.m[1] << "," << a2.m[2] << "}\n";
              std::cout << "  ax3: {" << a3.m[0] << "," << a3.m[1] << "," << a3.m[2] << "}\n";
              if (min_w > 0.0) {
                std::cout << "SUCCESS! ALL 4 WEIGHTS ARE POSITIVE!\n";
                return 0;
              }
            }
          }
        }
      }
    }
  }

  std::cout << "Finished search. Best min weight was: " << best_min_w << "\n";
  return 0;
}
