#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
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
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = yocto::normalize((tri_f[0] + tri_f[1] + tri_f[2]) / 3.0);

  std::cout << "dir_u0 = (" << dir_u0.x << ", " << dir_u0.y << ", " << dir_u0.z << ")\n";
  std::cout << "centroid = (" << centroid.x << ", " << centroid.y << ", " << centroid.z << ")\n";
  std::cout << "Angle(u0, centroid) = " << (std::acos(yocto::dot(dir_u0, centroid)) * 180 / M_PI) << " deg\n";

  std::vector<int> std_mixes = {0, 200, 400, 600, 800, 1000};

  // Sample views along the geodesic between centroid and dir_u0, and around dir_u0
  std::vector<ContactInfo> all_contacts;
  auto add_contacts_for_view = [&](const vec3 &v) {
    auto cts = Tube229::GenerateSilhouetteContacts(v, std_mixes);
    for (const auto &c : cts) {
      bool exists = false;
      for (const auto &ex : all_contacts) {
        if (ex.vertex == c.vertex && ex.edge_start == c.edge_start && ex.edge_finish == c.edge_finish &&
            ex.edge_start2 == c.edge_start2 && ex.edge_finish2 == c.edge_finish2 && ex.mix == c.mix) {
          exists = true; break;
        }
      }
      if (!exists) all_contacts.push_back(c);
    }
  };

  for (double t = 0.0; t <= 1.0; t += 0.1) {
    vec3 v = yocto::normalize(centroid * (1.0 - t) + dir_u0 * t);
    add_contacts_for_view(v);
  }

  std::cout << "Collected " << all_contacts.size() << " unique contacts from geodesic views.\n";

  auto raw_candidates = Tube229::GenerateCandidateTriples(tri, all_contacts, 1e-12);
  std::cout << "Generated " << raw_candidates.size() << " candidate triples.\n";

  double best_dot = -1.0;
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
      double dot = yocto::dot(dir_u0, uc_dir);
      double angle_deg = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
      if (dot > best_dot) {
        best_dot = dot;
        std::cout << "New closest zero-defect axis: dot = " << dot << " (angle = " << angle_deg << " deg), B = " << cert.B.ToString() << "\n";
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
