#include <iostream>
#include <iomanip>
#include <cmath>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {cnt0.x.ToDouble() / ax0.B.ToDouble(),
             cnt0.y.ToDouble() / ax0.B.ToDouble(),
             cnt0.z.ToDouble() / ax0.B.ToDouble()};

  // Test core axis candidates with Contact 2 on (14, 15, 15, 19):
  for (int m = 400; m <= 900; m += 50) {
    ContactInfo cc[3] = {
      MakeContact(3, 2, 2, 1, 150, 2),
      MakeContact(1, 4, 4, 8, 1000, 4),
      MakeContact(14, 15, 15, 19, m, 15)
    };
    AxisCertificate axc;
    BigVecQ3 cntc;
    BigRat delc;
    if (!Tube229::AuditAxis(tri, cc, &axc, &cntc, &delc, &err, BigRat(0))) continue;
    vec3 uc = {cntc.x.ToDouble() / axc.B.ToDouble(),
               cntc.y.ToDouble() / axc.B.ToDouble(),
               cntc.z.ToDouble() / axc.B.ToDouble()};
    double dot = yocto::dot(u0, uc) / (yocto::length(u0) * yocto::length(uc));
    double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
    std::cout << "m=" << m << ": dot=" << dot << ", angle=" << angle << " deg\n";
  }

  return 0;
}
