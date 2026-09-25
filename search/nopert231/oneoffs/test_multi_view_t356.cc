#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 v0 = vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};
  vec3 v1 = vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()};
  vec3 v2 = vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()};
  vec3 centroid = (v0 + v1 + v2) / 3.0;

  std::vector<vec3> sample_views = {centroid, v0, v1, v2};

  std::vector<int> fine_mixes = {
      0, 1, 10, 50, 100, 143, 200, 286, 300, 400, 429, 500,
      571, 600, 700, 714, 800, 857, 900, 950, 990, 999, 1000};

  std::vector<ContactInfo> all_contacts;
  for (const auto &view : sample_views) {
    auto raw = Tube229::GenerateSilhouetteContacts(view, fine_mixes);
    for (const auto &c : raw) {
      bool dup = false;
      for (const auto &ex : all_contacts) {
        if (ex.vertex == c.vertex &&
            ex.edge_start == c.edge_start &&
            ex.edge_finish == c.edge_finish &&
            ex.edge_start2 == c.edge_start2 &&
            ex.edge_finish2 == c.edge_finish2 &&
            ex.mix == c.mix) {
          dup = true;
          break;
        }
      }
      if (!dup) all_contacts.push_back(c);
    }
  }

  std::cout << "Total unique contacts from 4 views: " << all_contacts.size() << "\n";

  // Filter valid contacts:
  vec3 tri_f[3] = {v0, v1, v2};
  std::vector<ContactInfo> valid_contacts;
  for (const auto &c : all_contacts) {
    bool ok = true;
    for (int k = 0; k < 3; k++) {
      if (yocto::dot(Tube229::GetDoubleEdge(c), tri_f[k]) < 0) {
        ok = false; break;
      }
    }
    if (ok) valid_contacts.push_back(c);
  }
  std::cout << "Valid contacts: " << valid_contacts.size() << "\n";

  // Triangle 356 coordinates:
  // Base triangle 356 from test_triangulated_disk:
  // Let's re-generate base triangle 356:
  double c_cone = 0.035;
  double R_disk = std::sqrt(1.0 / (c_cone * c_cone) - 1.0);
  int N_rings = 40;
  // Point p is at x = 1.26511, y = -0.969618
  vec3 p = yocto::normalize(u0 + 1.26511 * e1 - 0.969618 * e2);

  // Check all candidate triples from valid_contacts against p:
  double max_dot_p = -1e9;
  int audited_zero_count = 0;
  for (size_t i = 0; i < valid_contacts.size(); i++) {
    for (size_t j = i + 1; j < valid_contacts.size(); j++) {
      for (size_t k = j + 1; k < valid_contacts.size(); k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        Tube229::CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;

        AxisCertificate cert;
        BigVecQ3 center;
        BigRat delta;
        if (!Tube229::AuditAxis(tri, triple, &cert, &center, &delta, &err, BigRat(0))) continue;
        audited_zero_count++;

        vec3 a = yocto::normalize(vec3{center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
        double d = yocto::dot(a, p);
        if (d > max_dot_p) {
          max_dot_p = d;
          std::cout << "Audited zero axis " << audited_zero_count << ": new max dot with p = " << d << "\n";
        }
      }
    }
  }

  std::cout << "Total audited zero axes: " << audited_zero_count << "\n";
  std::cout << "Max dot with p: " << max_dot_p << "\n";

  return 0;
}
