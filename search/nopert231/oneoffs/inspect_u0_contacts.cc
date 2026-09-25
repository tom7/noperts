#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
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
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(1, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 dir0 = yocto::normalize(u0);

  std::cout << "Inspecting all candidates generated for viewpoint dir0...\n";
  auto cands = Tube229::GenerateCandidatesForView(dir0, tri, false, 8, false);
  std::cout << "Generated " << cands.size() << " candidates for dir0.\n";

  for (size_t i = 0; i < cands.size(); i++) {
    ContactInfo contacts[3] = {cands[i].contacts[0], cands[i].contacts[1], cands[i].contacts[2]};
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    if (Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(1, 1000))) {
      vec3 uc = {center.x.ToDouble() / cert.B.ToDouble(),
                 center.y.ToDouble() / cert.B.ToDouble(),
                 center.z.ToDouble() / cert.B.ToDouble()};
      double dot = yocto::dot(dir0, yocto::normalize(uc));
      double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
      std::cout << "cand " << i << ": angle = " << std::fixed << std::setprecision(2) << angle
                << " deg, delta = " << delta.ToDouble() << "\n";
      for (int m = 0; m < 3; m++) {
        std::cout << "    MakeContact(" << contacts[m].edge_start << ", " << contacts[m].edge_finish
                  << ", " << contacts[m].edge_start2 << ", " << contacts[m].edge_finish2
                  << ", " << contacts[m].mix << ", " << contacts[m].vertex << "),\n";
      }
    }
  }

  return 0;
}
