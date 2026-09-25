#include <iostream>
#include <vector>
#include <algorithm>
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

  for (const auto &path : leaves) {
    std::cout << "\n========================================\n";
    std::cout << "Testing leaf " << path << " (depth " << path.size() << "):\n";
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
      std::cout << "Axis 0 audit failed: " << err << "\n";
      continue;
    }
    std::cout << "Axis 0: delta=" << delta0.ToDouble()
              << " center=(" << center0.x.ToDouble() << ", " << center0.y.ToDouble() << ", " << center0.z.ToDouble() << ")\n";

    std::vector<Tube229::AuditedAxis> candidates = Tube229::FindAllHullSupportAxes(tri, 500);

    vec3 c0_d = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};
    std::vector<vec3> cand_d(candidates.size());
    for (size_t i = 0; i < candidates.size(); i++) {
      cand_d[i] = {candidates[i].center.x.ToDouble(), candidates[i].center.y.ToDouble(), candidates[i].center.z.ToDouble()};
    }

    double best_inradius_d = 0.0;
    int best_i = -1, best_j = -1, best_k = -1;

    for (size_t i = 0; i < candidates.size(); i++) {
      for (size_t j = i + 1; j < candidates.size(); j++) {
        for (size_t k = j + 1; k < candidates.size(); k++) {
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
          double vol6 = std::abs(den);
          double inrad = vol6 / area_sum;

          if (inrad > best_inradius_d) {
            best_inradius_d = inrad;
            best_i = i; best_j = j; best_k = k;
          }
        }
      }
    }

    if (best_i >= 0) {
      BigVecQ3 exact_pts[4] = {center0, candidates[best_i].center, candidates[best_j].center, candidates[best_k].center};
      BigRat exact_inrad = Tube229::ExactTetrahedronAxisRadius(exact_pts);
      BigRat cover_rad = exact_inrad * BigRat(19, 20) * BigRat(4, 7);
      BigRat c_eff = cover_rad - delta0;
      std::cout << "  BEST inradius: " << best_inradius_d
                << " exact_axis_radius: " << exact_inrad.ToDouble()
                << " c_eff: " << c_eff.ToDouble() << "\n";
    }
  }
  return 0;
}
