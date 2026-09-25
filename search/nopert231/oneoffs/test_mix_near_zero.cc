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

  // Best triple was:
  // c0: v=9 e1=(8->9) e2=(9->10) mix=0
  // c1: v=10 e1=(9->10) e2=(10->15) mix=1000
  // c2: v=10 e1=(9->10) e2=(10->13) mix=1000

  double max_d = -1e9;
  int best_m0 = -1, best_m1 = -1, best_m2 = -1;

  for (int m0 = 0; m0 <= 50; m0 += 2) {
    for (int m1 = 950; m1 <= 1000; m1 += 2) {
      for (int m2 = 950; m2 <= 1000; m2 += 2) {
        ContactInfo triple[3] = {
          {8, 9, 9, 10, m0, 9},
          {9, 10, 10, 15, m1, 10},
          {9, 10, 10, 13, m2, 10}
        };
        Tube229::CandidateTriple cand;
        if (!Tube229::DoubleCheckAxis(tri, triple, &cand, 1e-12)) continue;
        double d = yocto::dot(cand.normalized_a, p);
        if (d > max_d) {
          max_d = d;
          best_m0 = m0; best_m1 = m1; best_m2 = m2;
          std::cout << "m0=" << m0 << " m1=" << m1 << " m2=" << m2 << " -> dot = " << d << "\n";
        }
      }
    }
  }

  std::cout << "Max dot found: " << max_d << " at (" << best_m0 << ", " << best_m1 << ", " << best_m2 << ")\n";
  return 0;
}
