#include <iostream>
#include <vector>
#include <cmath>
#include "nopert231.h"
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;
using vec2 = yocto::vec<double, 2>;

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

  // Edge is 10->13:
  vec3 v10 = Vertex(10);
  vec3 v13 = Vertex(13);
  vec3 edge = v13 - v10;

  // Let's test contacts with vertex 13:
  // In Tube229, what is the contact with vertex 13 and edge 10->13?
  // Let's create:
  ContactInfo c_v13;
  c_v13.vertex = 13;
  c_v13.edge_start = 10;
  c_v13.edge_finish = 13;
  c_v13.edge_start2 = 13;
  c_v13.edge_finish2 = 14;
  c_v13.mix = 1000; // 100% (10->13)

  vec3 edge_dir = Tube229::GetDoubleEdge(c_v13);
  vec3 tau = yocto::cross(edge_dir, v13);
  std::cout << "Dot(tau, p) = " << yocto::dot(tau, p) << "\n";

  // Now test all triples using c_v13 with other valid contacts:
  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 tri_f[3] = {
    vec3{c0.x.ToDouble(), c0.y.ToDouble(), c0.z.ToDouble()},
    vec3{c1.x.ToDouble(), c1.y.ToDouble(), c1.z.ToDouble()},
    vec3{c2.x.ToDouble(), c2.y.ToDouble(), c2.z.ToDouble()}
  };

  // Generate candidate triples including c_v13:
  std::vector<int> mixes = {0, 200, 500, 800, 1000};
  auto std_c = Tube229::GenerateSilhouetteContacts((tri_f[0]+tri_f[1]+tri_f[2])/3.0, mixes);
  std_c.push_back(c_v13);

  // Filter valid contacts:
  std::vector<ContactInfo> valid_c;
  for (const auto &c : std_c) {
    bool ok = true;
    for (int k = 0; k < 3; k++) {
      if (yocto::dot(Tube229::GetDoubleEdge(c), tri_f[k]) < 0) { ok = false; break; }
    }
    if (ok) valid_c.push_back(c);
  }

  std::cout << "Valid contacts: " << valid_c.size() << "\n";
  double max_dot_p = -1e9;
  for (size_t i = 0; i < valid_c.size(); i++) {
    for (size_t j = i + 1; j < valid_c.size(); j++) {
      ContactInfo triple[3] = {c_v13, valid_c[i], valid_c[j]};
      Tube229::CandidateTriple cand;
      if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;
      double d = yocto::dot(cand.normalized_a, p);
      if (d > max_dot_p) {
        max_dot_p = d;
        std::cout << "Triple with c_v13: dot with p = " << d << "\n";
      }
    }
  }

  std::cout << "Max dot with p using c_v13: " << max_dot_p << "\n";
  return 0;
}
