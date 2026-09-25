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
  std::vector<std::string> leaves = {
    "03121300",
    "0312130332",
    "03121303200",
    "03121303021",
    "03121303022",
    "03121303023"
  };

  BigRat c_cone(65, 1000); // 0.065

  for (const auto &path : leaves) {
    std::cout << "\n========================================\n";
    std::cout << "Testing leaf " << path << ":\n";
    TriangleQ tri = TriangleFromPath(path);

    ContactInfo c0[3] = {
      MakeContact(3, 2, 2, 1, 800, 2),
      MakeContact(1, 4, 4, 8, 800, 4),
      MakeContact(13, 14, 14, 15, 200, 14)
    };
    AxisCertificate ax0;
    BigVecQ3 center0;
    BigRat delta0;
    std::string err;
    if (!Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000))) {
      std::cout << "Axis 0 audit failed\n";
      continue;
    }

    std::vector<Tube229::AuditedAxis> candidates = Tube229::FindAllHullSupportAxes(tri, 500);

    // Pick best 3 complement axes from find_optimal_cage
    // Let's test different c_comp values:
    for (int c_comp_denom : {1000, 2000, 3000, 4000, 5000, 10000}) {
      BigRat c_comp(1, c_comp_denom);
      BigRat kappa = c_comp / c_cone;

      BigVecQ3 scaled_u0 = {center0.x * kappa, center0.y * kappa, center0.z * kappa};

      // Search among candidates for 3 complement axes that cage with scaled_u0:
      vec3 c0_d = {scaled_u0.x.ToDouble(), scaled_u0.y.ToDouble(), scaled_u0.z.ToDouble()};
      std::vector<vec3> cand_d(candidates.size());
      for (size_t i = 0; i < candidates.size(); i++) {
        cand_d[i] = {candidates[i].center.x.ToDouble(), candidates[i].center.y.ToDouble(), candidates[i].center.z.ToDouble()};
      }

      double best_inrad = 0.0;
      int bi = -1, bj = -1, bk = -1;

      for (size_t i = 0; i < std::min((size_t)100, candidates.size()); i++) {
        for (size_t j = i + 1; j < std::min((size_t)100, candidates.size()); j++) {
          for (size_t k = j + 1; k < std::min((size_t)100, candidates.size()); k++) {
            vec3 pts[4] = {c0_d, cand_d[i], cand_d[j], cand_d[k]};
            vec3 v0 = pts[0] - pts[3];
            vec3 v1 = pts[1] - pts[3];
            vec3 v2 = pts[2] - pts[3];
            vec3 w = -pts[3];
            double den = yocto::dot(v0, yocto::cross(v1, v2));
            if (std::abs(den) < 1e-12) continue;
            double lam0 = yocto::dot(w, yocto::cross(v1, v2)) / den;
            if (lam0 <= 1e-6) continue;
            double lam1 = yocto::dot(v0, yocto::cross(w, v2)) / den;
            if (lam1 <= 1e-6) continue;
            double lam2 = yocto::dot(v0, yocto::cross(v1, w)) / den;
            if (lam2 <= 1e-6) continue;
            double lam3 = 1.0 - lam0 - lam1 - lam2;
            if (lam3 <= 1e-6) continue;

            vec3 f0 = yocto::cross(pts[2] - pts[1], pts[3] - pts[1]);
            vec3 f1 = yocto::cross(pts[2] - pts[0], pts[3] - pts[0]);
            vec3 f2 = yocto::cross(pts[1] - pts[0], pts[3] - pts[0]);
            vec3 f3 = yocto::cross(pts[1] - pts[0], pts[2] - pts[0]);
            double area_sum = yocto::length(f0) + yocto::length(f1) + yocto::length(f2) + yocto::length(f3);
            if (area_sum < 1e-12) continue;
            double inrad = std::abs(den) / area_sum;
            if (inrad > best_inrad) {
              best_inrad = inrad;
              bi = i; bj = j; bk = k;
            }
          }
        }
      }

      if (bi >= 0) {
        BigVecQ3 exact_pts[4] = {scaled_u0, candidates[bi].center, candidates[bj].center, candidates[bk].center};
        BigRat exact_axis_r = Tube229::ExactTetrahedronAxisRadius(exact_pts);
        BigRat exact_cover_r = exact_axis_r * BigRat(19, 20) * BigRat(4, 7);
        std::cout << "  c_comp=1/" << c_comp_denom << " (kappa=" << kappa.ToDouble()
                  << "): inrad=" << best_inrad << " exact_cover_r=" << exact_cover_r.ToDouble()
                  << " needed=" << (c_comp + delta0).ToDouble()
                  << (exact_cover_r >= c_comp + delta0 ? " -> PASS!" : " -> fail") << "\n";
      }
    }
  }
  return 0;
}
