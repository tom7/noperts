#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  // Sample views across sphere
  std::vector<vec3> views;
  for (int x : {-1, 0, 1}) {
    for (int y : {-1, 0, 1}) {
      for (int z : {-1, 0, 1}) {
        if (x == 0 && y == 0 && z == 0) continue;
        views.push_back(yocto::normalize(vec3{(double)x, (double)y, (double)z}));
      }
    }
  }

  std::vector<Tube229::CandidateTriple> all_cands;
  for (const auto &v : views) {
    auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 6, true);
    for (const auto &c : cands) all_cands.push_back(c);
  }
  std::cout << "Generated " << all_cands.size() << " candidates across 26 views.\n";

  int zero_defect_count = 0;
  std::vector<vec3> zero_defect_centers;
  for (const auto &c : all_cands) {
    ContactInfo ct[3] = {c.contacts[0], c.contacts[1], c.contacts[2]};
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    if (Tube229::AuditAxis(tri, ct, &ax, &center, &delta, &err, BigRat(0))) {
      zero_defect_count++;
      zero_defect_centers.push_back({center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
    }
  }

  std::cout << "Zero-defect audited axes: " << zero_defect_count << "\n";
  if (!zero_defect_centers.empty()) {
    double min_x = 1e9, max_x = -1e9;
    double min_y = 1e9, max_y = -1e9;
    double min_z = 1e9, max_z = -1e9;
    for (const auto &c : zero_defect_centers) {
      min_x = std::min(min_x, c.x); max_x = std::max(max_x, c.x);
      min_y = std::min(min_y, c.y); max_y = std::max(max_y, c.y);
      min_z = std::min(min_z, c.z); max_z = std::max(max_z, c.z);
    }
    std::cout << "x range: [" << min_x << ", " << max_x << "]\n";
    std::cout << "y range: [" << min_y << ", " << max_y << "]\n";
    std::cout << "z range: [" << min_z << ", " << max_z << "]\n";
  }

  return 0;
}
