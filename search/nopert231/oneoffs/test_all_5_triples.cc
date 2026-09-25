#include <iostream>
#include <vector>
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
  }

  for (int i = 0; i < 5; i++) {
    for (int j = i + 1; j < 5; j++) {
      for (int k = j + 1; k < 5; k++) {
        BigVecQ3 c01 = {w[i].y * w[j].z - w[i].z * w[j].y,
                        w[i].z * w[j].x - w[i].x * w[j].z,
                        w[i].x * w[j].y - w[i].y * w[j].x};
        BigVecQ3 c12 = {w[j].y * w[k].z - w[j].z * w[k].y,
                        w[j].z * w[k].x - w[j].x * w[k].z,
                        w[j].x * w[k].y - w[j].y * w[k].x};
        BigVecQ3 c20 = {w[k].y * w[i].z - w[k].z * w[i].y,
                        w[k].z * w[i].x - w[k].x * w[i].z,
                        w[k].x * w[i].y - w[k].y * w[i].x};

        BigRat a0 = c12.x * u0.x + c12.y * u0.y + c12.z * u0.z;
        BigRat a1 = c20.x * u0.x + c20.y * u0.y + c20.z * u0.z;
        BigRat a2 = c01.x * u0.x + c01.y * u0.y + c01.z * u0.z;

        if ((a0 > 0 && a1 > 0 && a2 > 0) || (a0 < 0 && a1 < 0 && a2 < 0)) {
          BigRat sum = a0 + a1 + a2;
          BigRat mu0 = a0 / sum;
          BigRat mu1 = a1 / sum;
          BigRat mu2 = a2 / sum;
          BigRat lam_mu = mu0 * lams[i] + mu1 * lams[j] + mu2 * lams[k];
          std::cout << "Triple (" << chosen[i] << ", " << chosen[j] << ", " << chosen[k] << "): "
                    << "lam_mu = " << lam_mu.ToDouble()
                    << ", weights = (" << mu0.ToDouble() << ", " << mu1.ToDouble() << ", " << mu2.ToDouble() << ")\n";
        }
      }
    }
  }
  return 0;
}
