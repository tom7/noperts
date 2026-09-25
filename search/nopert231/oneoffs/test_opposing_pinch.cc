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

  double x = 1.264961, y = -0.9695687;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  std::cout << "Pinch point p = (" << p.x << ", " << p.y << ", " << p.z << ")\n";

  // Search opposing candidates for -p (i.e. candidates that have dot > 0 with p)
  auto cands = Tube229::FindOpposingCandidates(tri, p, 200, 0.0);
  std::cout << "Found " << cands.size() << " candidates with positive dot!\n";

  for (size_t i = 0; i < std::min((size_t)10, cands.size()); i++) {
    // Audit each candidate to see if it has zero support defect:
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    bool ok = Tube229::AuditAxis(tri, cands[i].contacts, &ax, &ctr, &del, &err, BigRat(0));
    std::cout << "  Cand " << i << ": dot = " << yocto::dot(p, cands[i].normalized_a)
              << ", zero defect? " << (ok ? "YES" : "NO: " + err) << "\n";
  }

  return 0;
}
