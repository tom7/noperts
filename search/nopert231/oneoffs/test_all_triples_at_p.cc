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

  double x = 1.265142, y = -0.9695975;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  auto c0 = tri.corners[0];
  auto c1 = tri.corners[1];
  auto c2 = tri.corners[2];
  vec3 centroid = vec3{
    (c0.x.ToDouble() + c1.x.ToDouble() + c2.x.ToDouble()) / 3.0,
    (c0.y.ToDouble() + c1.y.ToDouble() + c2.y.ToDouble()) / 3.0,
    (c0.z.ToDouble() + c1.z.ToDouble() + c2.z.ToDouble()) / 3.0
  };

  std::vector<int> fine_mixes = {0, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000};
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, fine_mixes);
  std::cout << "Testing triples of " << contacts.size() << " contacts...\n";

  double best_dot = -1e9;
  int best_i = -1, best_j = -1, best_k = -1;
  int valid_count = 0;

  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        ContactInfo sel[3] = {contacts[i], contacts[j], contacts[k]};
        Tube229::CandidateTriple cand;
        if (Tube229::DoubleCheckAxis(tri, sel, &cand, 1e-12)) {
          valid_count++;
          double d = yocto::dot(p, cand.normalized_a);
          if (d > best_dot) {
            best_dot = d;
            best_i = i; best_j = j; best_k = k;
          }
        }
      }
    }
  }

  std::cout << "Valid candidates found: " << valid_count << "\n";
  std::cout << "Best dot with p: " << best_dot << "\n";
  if (best_i >= 0) {
    ContactInfo sel[3] = {contacts[best_i], contacts[best_j], contacts[best_k]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    bool ok = Tube229::AuditAxis(tri, sel, &ax, &ctr, &del, &err, BigRat(0));
    std::cout << "Audited with zero defect? " << (ok ? "YES" : "NO: " + err) << "\n";
  }

  return 0;
}
