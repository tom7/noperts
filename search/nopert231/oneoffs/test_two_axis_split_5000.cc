#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  double norm_u0 = std::sqrt(u0_sq.ToDouble());
  vec3 u0_f = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_f, std::abs(u0_f.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_f, ex);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  struct Cand {
    int orig_idx;
    double lam;
    vec3 w;
  };

  std::vector<Cand> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      BigVecQ3 uc = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
      BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
      BigRat lam = dot / u0_sq;
      if (lam > 0) {
        BigVecQ3 w = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
        vec3 wf = {w.x.ToDouble(), w.y.ToDouble(), w.z.ToDouble()};
        cands.push_back({(int)i, lam.ToDouble(), wf});
      }
    }
  }

  std::cout << "Candidates with lam > 0: " << cands.size() << "\n";
  double c_cone = 0.018;
  double c_core = 0.003;
  double sin_alpha = std::sqrt(std::max(0.0, 1.0 - (c_cone / norm_u0) * (c_cone / norm_u0)));

  // Test pairs of candidates
  for (size_t i = 0; i < cands.size(); i++) {
    for (size_t j = i + 1; j < cands.size(); j++) {
      // Direction e in u0^perp from w1 towards w2
      vec3 w1 = cands[i].w;
      vec3 w2 = cands[j].w;
      // We want e such that dot(w1, e) > 0 and dot(w2, -e) > 0
      vec3 diff = w1 - w2;
      if (yocto::length(diff) < 1e-6) continue;
      vec3 e = yocto::normalize(diff);

      double sig1 = yocto::dot(w1, e);
      double sig2 = yocto::dot(w2, -e);
      if (sig1 <= 0 || sig2 <= 0) continue;

      vec3 z1 = w1 - sig1 * e;
      vec3 z2 = w2 - sig2 * (-e);

      double len_z1 = yocto::length(z1);
      double len_z2 = yocto::length(z2);

      double margin1 = cands[i].lam * c_cone - len_z1 * sin_alpha;
      double margin2 = cands[j].lam * c_cone - len_z2 * sin_alpha;

      if (margin1 >= c_core && margin2 >= c_core) {
        std::cout << "SUCCESS! 2-axis certificate found with axes "
                  << cands[i].orig_idx << " and " << cands[j].orig_idx << "!\n";
        std::cout << "  Axis 1: lam = " << cands[i].lam << ", |z1| = " << len_z1
                  << ", margin1 = " << margin1 << "\n";
        std::cout << "  Axis 2: lam = " << cands[j].lam << ", |z2| = " << len_z2
                  << ", margin2 = " << margin2 << "\n";
        std::cout << "  c_core target: " << c_core << "\n";
        return 0;
      }
    }
  }

  std::cout << "No pair satisfied margin >= " << c_core << "\n";
  return 0;
}
