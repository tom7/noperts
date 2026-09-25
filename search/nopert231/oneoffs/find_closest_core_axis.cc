#include <iostream>
#include <vector>
#include <string>
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
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Annular axis u0:
  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000))) return 1;
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_dir = yocto::normalize(u0);

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> std_mixes = {0, 200, 400, 600, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  auto raw_candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);
  std::cout << "Testing " << raw_candidates.size() << " candidate triples...\n";

  double best_dot = -1.0;
  Tube229::CandidateTriple best_cand;
  AxisCertificate best_cert;
  BigVecQ3 best_ctr;
  BigRat best_del;

  for (const auto &cand : raw_candidates) {
    ContactInfo test_contacts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, test_contacts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 uc = {ctr.x.ToDouble() / cert.B.ToDouble(),
                 ctr.y.ToDouble() / cert.B.ToDouble(),
                 ctr.z.ToDouble() / cert.B.ToDouble()};
      vec3 uc_dir = yocto::normalize(uc);
      double dot = yocto::dot(u0_dir, uc_dir);
      double angle_deg = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
      if (dot > best_dot) {
        best_dot = dot;
        best_cand = cand;
        best_cert = cert;
        best_ctr = ctr;
        best_del = del;
        std::cout << "New closest zero-defect axis: dot = " << dot << " (angle = " << angle_deg << " deg)\n";
        for (int m = 0; m < 3; m++) {
          const auto &c = cand.contacts[m];
          std::cout << "    [" << c.edge_start << "->" << c.edge_finish << ", "
                    << c.edge_start2 << "->" << c.edge_finish2 << ", mix " << c.mix << ", v " << c.vertex << "]\n";
        }
      }
    }
  }

  return 0;
}
