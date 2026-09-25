#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));

  BigRat c_cone("20/10000");   // 0.0020
  BigRat delta("115/100000");  // 0.00115
  BigRat c("140/100000");      // 0.00140

  BigRat v0_scale = (c + delta) / c_cone;
  BigVecQ3 v0 = ctr_ann * v0_scale;
  vec3 v0_f = {v0.x.ToDouble(), v0.y.ToDouble(), v0.z.ToDouble()};

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
    for (const auto &cand : cands) all_cands.push_back(cand);
  }

  std::vector<vec3> pts;
  pts.push_back(v0_f); // index 0 is v0

  std::vector<int> cand_map;
  cand_map.push_back(-1);

  for (size_t i = 0; i < all_cands.size(); i++) {
    ContactInfo ct[3] = {all_cands[i].contacts[0], all_cands[i].contacts[1], all_cands[i].contacts[2]};
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat ax_delta;
    std::string fail;
    if (Tube229::AuditAxis(tri, ct, &ax, &center, &ax_delta, &fail, BigRat(0))) {
      if (ax_delta <= delta) {
        pts.push_back({center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
        cand_map.push_back(i);
      }
    }
  }
  std::cout << "Total points for Wolfe: " << pts.size() << "\n";

  std::array<int, 4> simplex;
  vec3 sep_norm;
  bool enclosed = Tube229::FindBalancedTetrahedron(pts, &simplex, &sep_norm);
  std::cout << "Origin enclosed: " << (enclosed ? "YES" : "NO") << "\n";
  if (enclosed) {
    std::cout << "Simplex indices: " << simplex[0] << ", " << simplex[1] << ", " << simplex[2] << ", " << simplex[3] << "\n";
    bool has_v0 = (simplex[0] == 0 || simplex[1] == 0 || simplex[2] == 0 || simplex[3] == 0);
    std::cout << "Contains v0 (index 0): " << (has_v0 ? "YES" : "NO") << "\n";
  } else {
    std::cout << "Separating normal: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
  }

  return 0;
}
