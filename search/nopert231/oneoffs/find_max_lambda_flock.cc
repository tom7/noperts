#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 2000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;
  double u0_sq_d = u0_sq.ToDouble();
  vec3 u0_d = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};

  struct AxisData {
    int orig_idx;
    double lam;
    vec3 w;
  };
  std::vector<AxisData> zd_axes;

  for (size_t i = 0; i < axes.size(); i++) {
    ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0))) {
      vec3 uc = {ctr.x.ToDouble() / cert.B.ToDouble(),
                 ctr.y.ToDouble() / cert.B.ToDouble(),
                 ctr.z.ToDouble() / cert.B.ToDouble()};
      double dot = yocto::dot(u0_d, uc);
      double lam = dot / u0_sq_d;
      vec3 w = uc - (float)lam * u0_d;
      zd_axes.push_back({(int)i, lam, w});
    }
  }

  std::cout << "Audited zero-defect axes: " << zd_axes.size() << "\n";

  double best_lam_mu = -1e9;
  int best_triple[3] = {-1, -1, -1};
  double best_weights[3] = {0};

  // Search triples
  int N = zd_axes.size();
  for (int i = 0; i < N; i++) {
    for (int j = i + 1; j < N; j++) {
      vec3 cross_ij = yocto::cross(zd_axes[i].w, zd_axes[j].w);
      double z_ij = yocto::dot(cross_ij, u0_d);
      for (int k = j + 1; k < N; k++) {
        vec3 cross_jk = yocto::cross(zd_axes[j].w, zd_axes[k].w);
        double a0 = yocto::dot(cross_jk, u0_d);
        vec3 cross_ki = yocto::cross(zd_axes[k].w, zd_axes[i].w);
        double a1 = yocto::dot(cross_ki, u0_d);
        double a2 = z_ij;

        if ((a0 > 0 && a1 > 0 && a2 > 0) || (a0 < 0 && a1 < 0 && a2 < 0)) {
          double sum = a0 + a1 + a2;
          double mu0 = a0 / sum;
          double mu1 = a1 / sum;
          double mu2 = a2 / sum;
          double lam_mu = mu0 * zd_axes[i].lam + mu1 * zd_axes[j].lam + mu2 * zd_axes[k].lam;
          if (lam_mu > best_lam_mu) {
            best_lam_mu = lam_mu;
            best_triple[0] = zd_axes[i].orig_idx;
            best_triple[1] = zd_axes[j].orig_idx;
            best_triple[2] = zd_axes[k].orig_idx;
            best_weights[0] = mu0;
            best_weights[1] = mu1;
            best_weights[2] = mu2;
          }
        }
      }
    }
  }

  std::cout << "Best lambda_mu = " << best_lam_mu << "\n";
  if (best_triple[0] >= 0) {
    std::cout << "Triple: " << best_triple[0] << ", " << best_triple[1] << ", " << best_triple[2] << "\n";
    std::cout << "Weights: " << best_weights[0] << ", " << best_weights[1] << ", " << best_weights[2] << "\n";
    double c_cone = 0.018;
    std::cout << "Margin (lambda_mu * c_cone) = " << (best_lam_mu * c_cone) << "\n";
  }
  return 0;
}
