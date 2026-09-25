#include <iostream>
#include <vector>
#include <cmath>
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

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return a.x * (b.y * c.z - b.z * c.y) -
         a.y * (b.x * c.z - b.z * c.x) +
         a.z * (b.x * c.y - b.y * c.x);
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo cts0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  std::string err;
  if (!Tube229::AuditAxis(tri, cts0, &ax0, &ctr0, &del0, &err, BigRat(0))) return 1;
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto ToD = [](const BigVecQ3 &v) {
    return vec3(v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble());
  };
  vec3 tri_f[3] = {ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2])};
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  std::vector<int> std_mixes = {0, 200, 400, 600, 800, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, std_mixes);
  auto candidates = Tube229::GenerateCandidateTriples(tri, contacts, 1e-12);

  std::vector<vec3> u_list;
  for (const auto &cand : candidates) {
    ContactInfo cts[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 u = {ctr.x.ToDouble() / cert.B.ToDouble(),
                ctr.y.ToDouble() / cert.B.ToDouble(),
                ctr.z.ToDouble() / cert.B.ToDouble()};
      u_list.push_back(u);
    }
  }
  std::cout << "Valid axes: " << u_list.size() << "\n";

  // Check if p0 and any u1, u2, u3 contain 0
  // Note: p0 is along u0!
  // conv(p0, u1, u2, u3) contains 0 iff there exist weights alpha_0, alpha_1, alpha_2, alpha_3 > 0
  // such that alpha_0 * p0 + alpha_1 * u1 + alpha_2 * u2 + alpha_3 * u3 = 0.
  // Since p0 = c * u0 with c > 0, this is equivalent to:
  // there exist beta_0, beta_1, beta_2, beta_3 > 0 such that beta_0 * u0 + beta_1 * u1 + beta_2 * u2 + beta_3 * u3 = 0!
  // In other words, DOES -u0 LIE IN THE CONE OF (u1, u2, u3)?!
  vec3 neg_u0 = -u0;
  int cone_hits = 0;
  for (size_t i = 0; i < u_list.size(); i += 10) {
    for (size_t j = i + 1; j < u_list.size(); j += 10) {
      for (size_t k = j + 1; k < u_list.size(); k += 10) {
        vec3 u1 = u_list[i], u2 = u_list[j], u3 = u_list[k];
        double det = Det3(u1, u2, u3);
        if (std::abs(det) < 1e-12) continue;
        double a1 = Det3(neg_u0, u2, u3) / det;
        double a2 = Det3(u1, neg_u0, u3) / det;
        double a3 = Det3(u1, u2, neg_u0) / det;
        if (a1 > 0 && a2 > 0 && a3 > 0) {
          cone_hits++;
          if (cone_hits == 1) {
            std::cout << "FOUND CONE HIT with (" << i << ", " << j << ", " << k << ")!\n";
          }
        }
      }
    }
  }
  std::cout << "Total cone hits: " << cone_hits << "\n";
  return 0;
}
