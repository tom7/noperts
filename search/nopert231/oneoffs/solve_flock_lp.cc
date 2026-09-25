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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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

  struct Cand {
    int orig_idx;
    BigRat lam;
    BigRat wx, wy; // 2D coordinates in (ex, ey)
    double lam_d, wx_d, wy_d;
  };

  std::vector<Cand> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      BigVecQ3 uc = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
      BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
      BigRat lam = dot / u0_sq;
      BigVecQ3 w = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
      vec3 wf = {w.x.ToDouble(), w.y.ToDouble(), w.z.ToDouble()};
      double x = yocto::dot(wf, ex);
      double y = yocto::dot(wf, ey);
      cands.push_back({(int)i, lam, BigRat(0), BigRat(0), lam.ToDouble(), x, y});
    }
  }

  std::cout << "Audited zero-defect axes: " << cands.size() << "\n";

  // Search all triples that contain (0, 0) in 2D
  double best_lam_mu = -1e9;
  int best_triple[3] = {-1, -1, -1};
  double best_mu[3] = {0};

  int N = cands.size();
  for (int i = 0; i < N; i++) {
    for (int j = i + 1; j < N; j++) {
      // 2D cross product of w_i and w_j
      double z_ij = cands[i].wx_d * cands[j].wy_d - cands[i].wy_d * cands[j].wx_d;
      for (int k = j + 1; k < N; k++) {
        double a0 = cands[j].wx_d * cands[k].wy_d - cands[j].wy_d * cands[k].wx_d;
        double a1 = cands[k].wx_d * cands[i].wy_d - cands[k].wy_d * cands[i].wx_d;
        double a2 = z_ij;

        if ((a0 > 1e-12 && a1 > 1e-12 && a2 > 1e-12) ||
            (a0 < -1e-12 && a1 < -1e-12 && a2 < -1e-12)) {
          double sum = a0 + a1 + a2;
          double mu0 = a0 / sum;
          double mu1 = a1 / sum;
          double mu2 = a2 / sum;
          double lam_mu = mu0 * cands[i].lam_d + mu1 * cands[j].lam_d + mu2 * cands[k].lam_d;
          if (lam_mu > best_lam_mu) {
            best_lam_mu = lam_mu;
            best_triple[0] = cands[i].orig_idx;
            best_triple[1] = cands[j].orig_idx;
            best_triple[2] = cands[k].orig_idx;
            best_mu[0] = mu0;
            best_mu[1] = mu1;
            best_mu[2] = mu2;
          }
        }
      }
    }
  }

  std::cout << "Optimal LP solution among ALL 1455 zero-defect axes:\n";
  std::cout << "Best lambda_mu = " << best_lam_mu << "\n";
  if (best_triple[0] >= 0) {
    std::cout << "Triple: " << best_triple[0] << ", " << best_triple[1] << ", " << best_triple[2] << "\n";
    std::cout << "Weights: " << best_mu[0] << ", " << best_mu[1] << ", " << best_mu[2] << "\n";
    double c_cone = 0.018;
    std::cout << "Margin at c_cone = 0.018: " << (best_lam_mu * c_cone) << "\n";
    std::cout << "Triangle delta: " << del0.ToDouble() << "\n";
  }
  return 0;
}
