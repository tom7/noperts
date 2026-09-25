#include <iostream>
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

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Target Axis 0:
  ContactInfo c0_orig[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 cnt0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_orig, &ax0, &cnt0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {cnt0.x.ToDouble() / ax0.B.ToDouble(),
             cnt0.y.ToDouble() / ax0.B.ToDouble(),
             cnt0.z.ToDouble() / ax0.B.ToDouble()};

  // Silhouette vertices for Contact 2:
  struct Cand {
    int s1, f1, s2, f2, v;
  };
  std::vector<Cand> cands = {
    {4, 8, 8, 9, 8},
    {8, 9, 9, 10, 9},
    {9, 10, 10, 15, 10},
    {10, 15, 15, 19, 15},
    {15, 19, 19, 3, 19},
    {19, 3, 3, 2, 3}
  };

  std::cout << "Testing silhouette contacts for Contact 2 with BigRat(0) defect:\n";
  for (const auto& cand : cands) {
    for (int m = 0; m <= 1000; m += 100) {
      ContactInfo c[3] = {
        MakeContact(3, 2, 2, 1, 150, 2),
        MakeContact(1, 4, 4, 8, 1000, 4),
        MakeContact(cand.s1, cand.f1, cand.s2, cand.f2, m, cand.v)
      };
      AxisCertificate ax;
      BigVecQ3 cnt;
      BigRat del;
      if (Tube229::AuditAxis(tri, c, &ax, &cnt, &del, &err, BigRat(0))) {
        vec3 uc = {cnt.x.ToDouble() / ax.B.ToDouble(),
                   cnt.y.ToDouble() / ax.B.ToDouble(),
                   cnt.z.ToDouble() / ax.B.ToDouble()};
        double dot = yocto::dot(u0, uc) / (yocto::length(u0) * yocto::length(uc));
        double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
        std::cout << "v=" << cand.v << " m=" << m << " OK! dot=" << dot << " angle=" << angle
                  << " deg, B=" << ax.B.ToDouble() << ", del=" << del.ToDouble() << "\n";
      }
    }
  }

  return 0;
}
