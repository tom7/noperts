#include <iostream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0_sq = yocto::dot(u0, u0);
  vec3 E1 = {1.0, 0.0, -u0.x / u0.z};
  vec3 E2 = {0.0, 1.0, -u0.y / u0.z};
  vec3 P0 = u0 / norm_u0_sq;

  double X = 18.6877, Y = -23.5388;
  vec3 p = P0 + X * E1 + Y * E2;
  vec3 a = yocto::normalize(p);

  std::cout << "Calling GenerateCandidatesForView at a...\n";
  auto cands = Tube229::GenerateCandidatesForView(a, tri, false, 8, true);
  std::cout << "Generated " << cands.size() << " candidates.\n";

  double box_delta = 234013.0 / 1000000000.0;
  double best_dot = -1.0;
  for (const auto &cand : cands) {
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    std::string err;
    ContactInfo contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
      if (del.ToDouble() <= box_delta) {
        vec3 v = {ctr.x.ToDouble() / cert.B.ToDouble(),
                  ctr.y.ToDouble() / cert.B.ToDouble(),
                  ctr.z.ToDouble() / cert.B.ToDouble()};
        double d = yocto::dot(a, v);
        if (d > best_dot) {
          best_dot = d;
          std::cout << "New best dot: " << best_dot << " (delta=" << del.ToDouble() << ")\n";
          std::cout << "Contacts: "
                    << cand.contacts[0].vertex << "(mix=" << cand.contacts[0].mix << ") "
                    << cand.contacts[1].vertex << "(mix=" << cand.contacts[1].mix << ") "
                    << cand.contacts[2].vertex << "(mix=" << cand.contacts[2].mix << ")\n";
        }
      }
    }
  }

  std::cout << "Final best dot at (" << X << ", " << Y << "): " << best_dot << "\n";
  std::cout << "box.delta = " << box_delta << "\n";
  std::cout << "Margin over box.delta = " << (best_dot - box_delta) << "\n";

  return 0;
}
