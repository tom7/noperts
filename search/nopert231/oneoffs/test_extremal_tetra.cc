#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  std::vector<vec3> views;
  for (int x = -1; x <= 1; x++) {
    for (int y = -1; y <= 1; y++) {
      for (int z = -1; z <= 1; z++) {
        if (x == 0 && y == 0 && z == 0) continue;
        views.push_back(yocto::normalize(vec3{(float)x, (float)y, (float)z}));
      }
    }
  }

  std::vector<Tube229::CandidateTriple> all_cands;
  for (const auto &v : views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 6, true);
    for (const auto &c : cands) all_cands.push_back(c);
  }

  std::vector<Tube229::CandidateTriple> zero_defect_cands;
  std::vector<vec3> zero_defect_centers;
  std::vector<vec3> normalized_axes;
  std::string err;
  for (const auto &c : all_cands) {
    ContactInfo ct[3] = {c.contacts[0], c.contacts[1], c.contacts[2]};
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, ct, &ax, &ctr, &del, &err, BigRat(0))) {
      zero_defect_cands.push_back(c);
      zero_defect_centers.push_back({ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
      normalized_axes.push_back(c.normalized_a);
    }
  }
  std::cout << "Zero-defect cands: " << zero_defect_cands.size() << "\n";

  std::array<int, 4> indices;
  bool ok_norm = Tube229::FindExtremalTetrahedron(normalized_axes, &indices);
  std::cout << "FindExtremalTetrahedron on normalized_a: " << (ok_norm ? "SUCCESS!" : "FAILED") << "\n";
  if (ok_norm) {
    std::cout << "Indices: " << indices[0] << ", " << indices[1] << ", " << indices[2] << ", " << indices[3] << "\n";
    for (int i = 0; i < 4; i++) {
      vec3 p = zero_defect_centers[indices[i]];
      std::cout << "  center " << i << " = (" << p.x << ", " << p.y << ", " << p.z << ")\n";
    }
  }

  bool ok_ctr = Tube229::FindExtremalTetrahedron(zero_defect_centers, &indices);
  std::cout << "FindExtremalTetrahedron on centers: " << (ok_ctr ? "SUCCESS!" : "FAILED") << "\n";
  if (ok_ctr) {
    std::cout << "Indices: " << indices[0] << ", " << indices[1] << ", " << indices[2] << ", " << indices[3] << "\n";
    for (int i = 0; i < 4; i++) {
      vec3 p = zero_defect_centers[indices[i]];
      std::cout << "  center " << i << " = (" << p.x << ", " << p.y << ", " << p.z << ")\n";
    }
  }

  return 0;
}
