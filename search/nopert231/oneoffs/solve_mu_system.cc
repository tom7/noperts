#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  int chosen[] = {3054, 119, 3063, 22, 24};

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigRat u0_sq = u0.x * u0.x + u0.y * u0.y + u0.z * u0.z;

  std::vector<BigVecQ3> w;
  std::vector<BigRat> lams;

  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    BigVecQ3 uc = {ctr.x / cert.B, ctr.y / cert.B, ctr.z / cert.B};
    BigRat dot = u0.x * uc.x + u0.y * uc.y + u0.z * uc.z;
    BigRat lam = dot / u0_sq;
    BigVecQ3 wi = {uc.x - lam * u0.x, uc.y - lam * u0.y, uc.z - lam * u0.z};
    w.push_back(wi);
    lams.push_back(lam);
    std::cout << "Axis " << idx << ": lam = " << lam.ToDouble()
              << ", w = (" << wi.x.ToDouble() << ", " << wi.y.ToDouble() << ", " << wi.z.ToDouble() << ")\n";
  }

  // We want non-negative weights mu_0, ..., mu_4 such that:
  // sum mu_m w_m = 0
  // sum mu_m = 1
  // and lambda_mu = sum mu_m lam_m > 0.
  // This is a 2D LP because w_m lies in u0^perp!
  // Let's test random convex combinations or grid search over the simplex:
  double best_lam_mu = -1;
  double best_mu[5] = {0};

  for (int m0 = 0; m0 <= 100; m0++) {
    for (int m1 = 0; m1 <= 100 - m0; m1++) {
      for (int m2 = 0; m2 <= 100 - m0 - m1; m2++) {
        for (int m3 = 0; m3 <= 100 - m0 - m1 - m2; m3++) {
          int m4 = 100 - m0 - m1 - m2 - m3;
          double mu[5] = {m0 / 100.0, m1 / 100.0, m2 / 100.0, m3 / 100.0, m4 / 100.0};
          vec3 w_sum = {0, 0, 0};
          double lam_sum = 0;
          for (int k = 0; k < 5; k++) {
            w_sum.x += mu[k] * w[k].x.ToDouble();
            w_sum.y += mu[k] * w[k].y.ToDouble();
            w_sum.z += mu[k] * w[k].z.ToDouble();
            lam_sum += mu[k] * lams[k].ToDouble();
          }
          if (yocto::length(w_sum) < 0.001) {
            if (lam_sum > best_lam_mu) {
              best_lam_mu = lam_sum;
              for (int k = 0; k < 5; k++) best_mu[k] = mu[k];
            }
          }
        }
      }
    }
  }

  std::cout << "Best lambda_mu = " << best_lam_mu << "\n";
  if (best_lam_mu > 0) {
    std::cout << "Weights: ";
    for (int k = 0; k < 5; k++) std::cout << "mu[" << k << "] = " << best_mu[k] << " ";
    std::cout << "\n";
    double c_cone = 0.018;
    std::cout << "lambda_mu * c_cone = " << (best_lam_mu * c_cone) << "\n";
  }
  return 0;
}
