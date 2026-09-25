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

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Base parameters:
  int m0[3] = {420, 1000, 425};
  int m1[3] = {0, 600, 740};
  int m2[3] = {200, 990, 0};
  int m3[3] = {650, 220, 640};

  auto Eval = [&](int m0_0, int m0_2, int m1_0, int m1_1, int m1_2,
                  int m2_0, int m2_1, int m2_2, int m3_0, int m3_1, int m3_2,
                  double w_out[4]) -> double {
    ContactInfo c0[3] = {
      MakeContact(3, 2, 2, 1, m0_0, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(14, 15, 15, 19, m0_2, 15)
    };
    ContactInfo c1[3] = {
      MakeContact(2, 1, 1, 4, m1_0, 1),
      MakeContact(10, 15, 15, 19, m1_1, 15),
      MakeContact(19, 3, 3, 2, m1_2, 3)
    };
    ContactInfo c2[3] = {
      MakeContact(2, 1, 1, 0, m2_0, 1),
      MakeContact(10, 15, 15, 19, m2_1, 15),
      MakeContact(10, 15, 15, 19, m2_2, 15)
    };
    ContactInfo c3[3] = {
      MakeContact(3, 2, 2, 1, m3_0, 2),
      MakeContact(8, 9, 9, 10, m3_1, 9),
      MakeContact(3, 2, 2, 1, m3_2, 2)
    };
    AxisCertificate ax0, ax1, ax2, ax3;
    BigVecQ3 cnt0, cnt1, cnt2, cnt3;
    BigRat del0, del1, del2, del3;
    if (!Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0))) return -999.0;
    if (!Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &del1, &err, BigRat(0))) return -999.0;
    if (!Tube229::AuditAxis(tri, c2, &ax2, &cnt2, &del2, &err, BigRat(0))) return -999.0;
    if (!Tube229::AuditAxis(tri, c3, &ax3, &cnt3, &del3, &err, BigRat(0))) return -999.0;

    BigVecQ3 u0 = cnt0 / ax0.B;
    BigVecQ3 u1 = cnt1 / ax1.B;
    BigVecQ3 u2 = cnt2 / ax2.B;
    BigVecQ3 u3 = cnt3 / ax3.B;
    vec3 v0 = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};
    vec3 v1 = {u1.x.ToDouble(), u1.y.ToDouble(), u1.z.ToDouble()};
    vec3 v2 = {u2.x.ToDouble(), u2.y.ToDouble(), u2.z.ToDouble()};
    vec3 v3 = {u3.x.ToDouble(), u3.y.ToDouble(), u3.z.ToDouble()};

    double w[4];
    if (!SolveTetraOriginDouble(v0, v1, v2, v3, w)) return -999.0;
    if (w_out) {
      w_out[0] = w[0]; w_out[1] = w[1]; w_out[2] = w[2]; w_out[3] = w[3];
    }
    return std::min({w[0], w[1], w[2], w[3]});
  };

  double w_base[4];
  double base_score = Eval(m0[0], m0[2], m1[0], m1[1], m1[2],
                           m2[0], m2[1], m2[2], m3[0], m3[1], m3[2], w_base);
  std::cout << "Base score: " << std::setprecision(10) << base_score
            << " (w0=" << w_base[0] << ", w1=" << w_base[1]
            << ", w2=" << w_base[2] << ", w3=" << w_base[3] << ")\n\n";

  // Check 1D sensitivities:
  auto TestVar = [&](const std::string& name, int* ptr, int delta) {
    int orig = *ptr;
    *ptr = orig + delta;
    double s = Eval(m0[0], m0[2], m1[0], m1[1], m1[2],
                    m2[0], m2[1], m2[2], m3[0], m3[1], m3[2], nullptr);
    std::cout << "  " << name << " -> " << *ptr << " (delta " << delta << "): score = " << s
              << " (diff = " << (s - base_score) << ")\n";
    *ptr = orig;
  };

  std::cout << "Sensitivities:\n";
  TestVar("m0_0", &m0[0], +20);
  TestVar("m0_0", &m0[0], -20);
  TestVar("m0_2", &m0[2], +10);
  TestVar("m0_2", &m0[2], -10);
  TestVar("m1_0", &m1[0], +10);
  TestVar("m1_1", &m1[1], +20);
  TestVar("m1_1", &m1[1], -20);
  TestVar("m1_2", &m1[2], +20);
  TestVar("m1_2", &m1[2], -20);
  TestVar("m2_0", &m2[0], +20);
  TestVar("m2_0", &m2[0], -20);
  TestVar("m2_1", &m2[1], +10);
  TestVar("m2_1", &m2[1], -10);
  TestVar("m2_2", &m2[2], +15);
  TestVar("m3_0", &m3[0], +25);
  TestVar("m3_0", &m3[0], -25);
  TestVar("m3_1", &m3[1], +10);
  TestVar("m3_1", &m3[1], -10);
  TestVar("m3_2", &m3[2], +15);
  TestVar("m3_2", &m3[2], -15);

  return 0;
}
