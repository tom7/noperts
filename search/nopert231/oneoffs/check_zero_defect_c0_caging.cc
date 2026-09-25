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

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Axes 1, 2, 3 from the winning quad:
  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 50, 1),
    MakeContact(10, 15, 15, 19, 800, 15),
    MakeContact(19, 3, 3, 2, 950, 3)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 1000, 1),
    MakeContact(8, 9, 9, 10, 1000, 9),
    MakeContact(9, 10, 10, 15, 343, 10)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 113, 2),
    MakeContact(1, 4, 4, 8, 320, 4),
    MakeContact(10, 15, 15, 19, 150, 15)
  };

  AxisCertificate ax1, ax2, ax3;
  BigVecQ3 cnt1, cnt2, cnt3;
  BigRat del1, del2, del3;
  std::string err;
  Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &cnt2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &cnt3, &del3, &err, BigRat(0));

  vec3 u1 = {cnt1.x.ToDouble() / ax1.B.ToDouble(),
             cnt1.y.ToDouble() / ax1.B.ToDouble(),
             cnt1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 u2 = {cnt2.x.ToDouble() / ax2.B.ToDouble(),
             cnt2.y.ToDouble() / ax2.B.ToDouble(),
             cnt2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 u3 = {cnt3.x.ToDouble() / ax3.B.ToDouble(),
             cnt3.y.ToDouble() / ax3.B.ToDouble(),
             cnt3.z.ToDouble() / ax3.B.ToDouble()};

  std::cout << "Testing zero-defect Axis 0 candidates (m in 400..900) for caging:\n";
  for (int m = 400; m <= 900; m += 50) {
    ContactInfo c0[3] = {
      MakeContact(3, 2, 2, 1, 150, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(14, 15, 15, 19, m, 15)
    };
    AxisCertificate ax0;
    BigVecQ3 cnt0;
    BigRat del0;
    if (!Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(0))) continue;
    BigVecQ3 u0 = {cnt0.x / ax0.B, cnt0.y / ax0.B, cnt0.z / ax0.B};
    BigVecQ3 u1_q = {cnt1.x / ax1.B, cnt1.y / ax1.B, cnt1.z / ax1.B};
    BigVecQ3 u2_q = {cnt2.x / ax2.B, cnt2.y / ax2.B, cnt2.z / ax2.B};
    BigVecQ3 u3_q = {cnt3.x / ax3.B, cnt3.y / ax3.B, cnt3.z / ax3.B};

    BigVecQ3 d1 = u1_q - u0;
    BigVecQ3 d2 = u2_q - u0;
    BigVecQ3 d3 = u3_q - u0;
    BigVecQ3 c23 = BigVecQ3::Cross(d2, d3);
    BigRat det = BigVecQ3::Dot(d1, c23);

    BigVecQ3 dp = BigVecQ3{BigRat(0), BigRat(0), BigRat(0)} - u0;
    BigRat l1 = BigVecQ3::Dot(dp, c23) / det;
    BigRat l2 = BigVecQ3::Dot(d1, BigVecQ3::Cross(dp, d3)) / det;
    BigRat l3 = BigVecQ3::Dot(d1, BigVecQ3::Cross(d2, dp)) / det;
    BigRat l0 = BigRat(1) - l1 - l2 - l3;

    std::cout << "m=" << m << ": B0=" << ax0.B.ToDouble()
              << ", weights = (" << l0.ToDouble() << ", " << l1.ToDouble() << ", "
              << l2.ToDouble() << ", " << l3.ToDouble() << ")\n";
  }

  return 0;
}
