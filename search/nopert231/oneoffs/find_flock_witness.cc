#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static double Det3(vec3 a, vec3 b, vec3 c) {
  return yocto::dot(a, yocto::cross(b, c));
}

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

  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  std::cout << "Hull support axes: " << axes.size() << "\n";

  struct Candidate {
    int orig_idx;
    AxisCertificate cert;
    BigVecQ3 ctr;
    BigRat del;
    BigRat lam;
    BigVecQ3 w;
    vec3 w_f;
    double lam_f;
  };

  std::vector<Candidate> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    // We require strictly zero defect across all vertices of triangle
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      BigVecQ3 uc = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
      BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
      BigRat lam = dot / u0_sq;
      if (lam > 0) {
        BigVecQ3 w = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
        vec3 wf = {w.x.ToDouble(), w.y.ToDouble(), w.z.ToDouble()};
        cands.push_back({(int)i, cert, ctr, del, lam, w, wf, lam.ToDouble()});
      }
    }
  }
  std::cout << "Zero-defect candidates with lam > 0: " << cands.size() << "\n";

  // We want to find 3 candidates i, j, k such that:
  // mu1 * w1 + mu2 * w2 + mu3 * w3 = 0 with mu1, mu2, mu3 > 0
  // In other words, in the plane perpendicular to u0, 0 is in the interior of triangle (w1, w2, w3).
  // Cross product (w1 x w2) points along u0 (or -u0).
  // For 0 to be inside conv(w1, w2, w3) in the plane perpendicular to u0,
  // all three cross products (w1 x w2), (w2 x w3), (w3 x w1) must have the same sign along u0!
  vec3 u0_f = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};

  int found = 0;
  double best_min_lam = 0;
  int best_triple[3] = {-1, -1, -1};

  for (size_t i = 0; i < cands.size(); i++) {
    for (size_t j = i + 1; j < cands.size(); j++) {
      for (size_t k = j + 1; k < cands.size(); k++) {
        vec3 c12 = yocto::cross(cands[i].w_f, cands[j].w_f);
        vec3 c23 = yocto::cross(cands[j].w_f, cands[k].w_f);
        vec3 c31 = yocto::cross(cands[k].w_f, cands[i].w_f);
        double s12 = yocto::dot(c12, u0_f);
        double s23 = yocto::dot(c23, u0_f);
        double s31 = yocto::dot(c31, u0_f);

        bool pos = (s12 > 1e-7 && s23 > 1e-7 && s31 > 1e-7);
        bool neg = (s12 < -1e-7 && s23 < -1e-7 && s31 < -1e-7);
        if (pos || neg) {
          found++;
          double min_lam = std::min({cands[i].lam_f, cands[j].lam_f, cands[k].lam_f});
          if (min_lam > best_min_lam) {
            best_min_lam = min_lam;
            best_triple[0] = i;
            best_triple[1] = j;
            best_triple[2] = k;
          }
        }
      }
    }
  }

  std::cout << "Found " << found << " valid 3-axis flocks surrounding u0 in u0^perp!\n";
  if (best_triple[0] >= 0) {
    auto &c1 = cands[best_triple[0]];
    auto &c2 = cands[best_triple[1]];
    auto &c3 = cands[best_triple[2]];
    std::cout << "Best flock: axes (" << c1.orig_idx << ", " << c2.orig_idx << ", " << c3.orig_idx << ")\n";
    std::cout << "  lam1 = " << c1.lam_f << ", lam2 = " << c2.lam_f << ", lam3 = " << c3.lam_f << "\n";
    std::cout << "  best_min_lam = " << best_min_lam << "\n";
  }
  return 0;
}
