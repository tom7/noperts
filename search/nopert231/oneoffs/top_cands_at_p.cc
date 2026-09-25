#include <iostream>
#include <vector>
#include <algorithm>
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

  auto cands = Tube229::GenerateCandidatesForView(centroid, tri, true, 4, true, 1e-12);
  std::vector<std::pair<double, int>> ranked;
  for (size_t i = 0; i < cands.size(); i++) {
    ranked.push_back({yocto::dot(p, cands[i].normalized_a), (int)i});
  }
  std::sort(ranked.rbegin(), ranked.rend());

  std::cout << "Top 10 candidates at p:\n";
  for (int i = 0; i < 10; i++) {
    int id = ranked[i].second;
    std::cout << "  [" << i << "] cand " << id << ": dot = " << ranked[i].first << "\n";
    for (int j = 0; j < 3; j++) {
      std::cout << "      c" << j << ": edge=(" << cands[id].contacts[j].edge_start << "->" << cands[id].contacts[j].edge_finish
                << "), edge2=(" << cands[id].contacts[j].edge_start2 << "->" << cands[id].contacts[j].edge_finish2
                << "), mix=" << cands[id].contacts[j].mix << ", v=" << cands[id].contacts[j].vertex << "\n";
    }
  }

  return 0;
}
