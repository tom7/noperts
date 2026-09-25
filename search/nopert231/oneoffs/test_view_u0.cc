#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

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
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  std::cout << "Testing views directly near dir_u0 and -dir_u0...\n";
  for (double sign : {1.0, -1.0}) {
    vec3 base_v = dir_u0 * sign;
    for (double dx = -0.2; dx <= 0.2; dx += 0.05) {
      for (double dy = -0.2; dy <= 0.2; dy += 0.05) {
        vec3 v = yocto::normalize(base_v + vec3{dx, dy, 0});
        auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, false);
        for (const auto &cand : cands) {
          ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
          AxisCertificate cert;
          BigVecQ3 center;
          BigRat delta;
          if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
            vec3 uc = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
            vec3 dir_uc = yocto::normalize(uc);
            double dot = yocto::dot(dir_u0, dir_uc);
            double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
            if (angle < 30.0) {
              std::cout << "CLOSE AXIS! angle = " << angle << " deg (dot = " << dot << ")\n";
              for (int m = 0; m < 3; m++) {
                std::cout << "  MakeContact(" << contacts[m].edge_start << ", " << contacts[m].edge_finish
                          << ", " << contacts[m].edge_start2 << ", " << contacts[m].edge_finish2
                          << ", " << contacts[m].mix << ", " << contacts[m].vertex << "),\n";
              }
              if (angle < 12.0) {
                std::cout << "SUCCESS! Angle < 12 degrees!\n";
                return 0;
              }
            }
          }
        }
      }
    }
  }
  std::cout << "Done grid around u0\n";
  return 0;
}
