#include <iostream>
#include <vector>
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

  double x = 1.26511, y = -0.969618;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 v0 = vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()};
  vec3 v1 = vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()};
  vec3 v2 = vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()};

  std::vector<vec3> sample_views;
  for (int i = 0; i <= 10; i++) {
    for (int j = 0; j <= 10 - i; j++) {
      double w0 = i / 10.0, w1 = j / 10.0, w2 = 1.0 - w0 - w1;
      sample_views.push_back(yocto::normalize(w0 * v0 + w1 * v1 + w2 * v2));
    }
  }

  std::vector<int> mixes = {0, 200, 333, 500, 666, 800, 1000};
  std::vector<ContactInfo> all_contacts;
  for (const auto &vw : sample_views) {
    auto sc = Tube229::GenerateSilhouetteContacts(vw, mixes);
    for (const auto &c : sc) {
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

  double max_dot_p = -1e9;
  ContactInfo best_triple[3];
  Tube229::CandidateTriple best_cand;
  for (size_t i = 0; i < valid_contacts.size(); i++) {
    for (size_t j = i + 1; j < valid_contacts.size(); j++) {
      for (size_t k = j + 1; k < valid_contacts.size(); k++) {
        ContactInfo triple[3] = {valid_contacts[i], valid_contacts[j], valid_contacts[k]};
        Tube229::CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;
        double d = yocto::dot(cand.normalized_a, p);
        if (d > max_dot_p) {
          max_dot_p = d;
          best_triple[0] = triple[0];
          best_triple[1] = triple[1];
          best_triple[2] = triple[2];
          best_cand = cand;
        }
      }
    }
  }

  std::cout << "Best triple dot with p: " << max_dot_p << "\n";
  for (int m = 0; m < 3; m++) {
    std::cout << "  c" << m << ": v=" << best_triple[m].vertex
              << " e1=(" << best_triple[m].edge_start << "->" << best_triple[m].edge_finish << ")"
              << " e2=(" << best_triple[m].edge_start2 << "->" << best_triple[m].edge_finish2 << ")"
              << " mix=" << best_triple[m].mix << "\n";
  }

  return 0;
}
