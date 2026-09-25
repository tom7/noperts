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
  std::string target = "031213002112122012121";
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
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  std::cout << "Searching for zero-defect axes near dir_u0...\n";
  double min_angle = 180.0;

  // To get an axis u parallel to u0, we sample views orthogonal to u0!
  vec3 perp1 = yocto::normalize(yocto::cross(dir_u0, vec3{1, 0, 0}));
  vec3 perp2 = yocto::normalize(yocto::cross(dir_u0, perp1));

  for (double phi = 0; phi < 2 * M_PI; phi += 0.1) {
    vec3 v = perp1 * std::cos(phi) + perp2 * std::sin(phi);
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 8, false);
    for (const auto &cand : cands) {
      ContactInfo c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
        vec3 u = {ctr.x.ToDouble() / cert.B.ToDouble(),
                  ctr.y.ToDouble() / cert.B.ToDouble(),
                  ctr.z.ToDouble() / cert.B.ToDouble()};
        double d = yocto::dot(yocto::normalize(u), dir_u0);
        double angle = std::acos(std::max(-1.0, std::min(1.0, d))) * 180.0 / M_PI;
        if (angle < min_angle) {
          min_angle = angle;
          std::cout << "New closest axis: angle = " << angle << " deg, dot = " << d << "\n";
          std::cout << "Contacts: \n";
          for (int i = 0; i < 3; i++) {
            std::cout << "  (" << cand.contacts[i].edge_start << "->" << cand.contacts[i].edge_finish
                      << ", " << cand.contacts[i].mix << ", v=" << cand.contacts[i].vertex << ")\n";
          }
        }
      }
    }
  }

  std::cout << "Closest zero-defect axis to u0 has angle = " << min_angle << " deg\n";
  return 0;
}
