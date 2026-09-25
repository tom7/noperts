#include <iostream>
#include <vector>
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
  std::string target = "03121303200";
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
  vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  std::cout << "dir_u0: " << dir_u0.x << ", " << dir_u0.y << ", " << dir_u0.z << "\n";

  for (int sgn : {1, -1}) {
    vec3 v = dir_u0 * (double)sgn;
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, true);
    std::cout << "sgn=" << sgn << ": found " << cands.size() << " candidates for view.\n";
    for (const auto &cand : cands) {
      ContactInfo c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
        vec3 v0 = {ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()};
        double d = yocto::dot(yocto::normalize(v0), dir_u0);
        double angle = std::acos(std::max(-1.0, std::min(1.0, d))) * 180.0 / M_PI;
        std::cout << "  Zero-defect axis: angle=" << angle << " deg, B=" << cert.B.ToString() << "\n";
      }
    }
  }
  return 0;
}
