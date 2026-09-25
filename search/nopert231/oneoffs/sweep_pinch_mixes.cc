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

  double best_dot = -1e9;
  int best_m1 = -1, best_m2 = -1;

  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      if (m1 == m2) continue;
      ContactInfo c[3] = {
        {2, 1, 1, 4, 0, 1},
        {14, 15, 15, 19, m1, 15},
        {14, 15, 15, 19, m2, 15}
      };
      Tube229::CandidateTriple cand;
      if (Tube229::DoubleCheckAxis(tri, c, &cand, 1e-12)) {
        double d = yocto::dot(p, cand.normalized_a);
        if (d > best_dot) {
          best_dot = d;
          best_m1 = m1;
          best_m2 = m2;
        }
      }
    }
  }

  std::cout << "Best dot at pinch vertex with fine mixes: " << best_dot
            << " at m1=" << best_m1 << ", m2=" << best_m2 << "\n";
  if (best_m1 >= 0) {
    ContactInfo c[3] = {
      {2, 1, 1, 4, 0, 1},
      {14, 15, 15, 19, best_m1, 15},
      {14, 15, 15, 19, best_m2, 15}
    };
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    bool ok = Tube229::AuditAxis(tri, c, &ax, &ctr, &del, &err, BigRat(0));
    std::cout << "Audited with zero defect? " << (ok ? "YES" : "NO: " + err) << "\n";
  }

  return 0;
}
