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

  std::cout << "Searching for candidates maximizing dot with p: (" << p.x << ", " << p.y << ", " << p.z << ")...\n";
  auto opposing = Tube229::FindOpposingCandidates(tri, -p, 20, 1e-12);
  std::cout << "Found " << opposing.size() << " opposing candidates.\n";

  for (size_t i = 0; i < opposing.size(); i++) {
    double d = yocto::dot(p, opposing[i].normalized_a);
    std::cout << "  [" << i << "] dot with p = " << d << "\n";
    for (int j = 0; j < 3; j++) {
      std::cout << "      c" << j << ": edge=(" << opposing[i].contacts[j].edge_start << "->" << opposing[i].contacts[j].edge_finish
                << "), edge2=(" << opposing[i].contacts[j].edge_start2 << "->" << opposing[i].contacts[j].edge_finish2
                << "), mix=" << opposing[i].contacts[j].mix << ", v=" << opposing[i].contacts[j].vertex << "\n";
    }
  }

  return 0;
}
