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

  int chosen[] = {119, 3063, 22};

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

  // We have 3 vectors w[0], w[1], w[2] in the 2D subspace u0^perp.
  // We want exact BigRat mu0, mu1, mu2 > 0 such that:
  // mu0 * w[0] + mu1 * w[1] + mu2 * w[2] = 0
  // mu0 + mu1 + mu2 = 1
  // In 2D, the cross product w[i] x w[j] along u0 gives the barycentric weights!
  // w0 x w1, w1 x w2, w2 x w0:
  BigVecQ3 c01 = {w[0].y * w[1].z - w[0].z * w[1].y,
                  w[0].z * w[1].x - w[0].x * w[1].z,
                  w[0].x * w[1].y - w[0].y * w[1].x};
  BigVecQ3 c12 = {w[1].y * w[2].z - w[1].z * w[2].y,
                  w[1].z * w[2].x - w[1].x * w[2].z,
                  w[1].x * w[2].y - w[1].y * w[2].x};
  BigVecQ3 c20 = {w[2].y * w[0].z - w[2].z * w[0].y,
                  w[2].z * w[0].x - w[2].x * w[0].z,
                  w[2].x * w[0].y - w[2].y * w[0].x};

  BigRat a0 = c12.x * u0.x + c12.y * u0.y + c12.z * u0.z;
  BigRat a1 = c20.x * u0.x + c20.y * u0.y + c20.z * u0.z;
  BigRat a2 = c01.x * u0.x + c01.y * u0.y + c01.z * u0.z;

  std::cout << "a0 = " << a0.ToString() << " (" << a0.ToDouble() << ")\n";
  std::cout << "a1 = " << a1.ToString() << " (" << a1.ToDouble() << ")\n";
  std::cout << "a2 = " << a2.ToString() << " (" << a2.ToDouble() << ")\n";

  // Check signs
  if ((a0 > 0 && a1 > 0 && a2 > 0) || (a0 < 0 && a1 < 0 && a2 < 0)) {
    BigRat sum = a0 + a1 + a2;
    BigRat mu0 = a0 / sum;
    BigRat mu1 = a1 / sum;
    BigRat mu2 = a2 / sum;
    std::cout << "\nEXACT BARYCENTRIC WEIGHTS FOUND!\n";
    std::cout << "mu0 = " << mu0.ToString() << "\n";
    std::cout << "mu1 = " << mu1.ToString() << "\n";
    std::cout << "mu2 = " << mu2.ToString() << "\n";

    BigRat lam_mu = mu0 * lams[0] + mu1 * lams[1] + mu2 * lams[2];
    std::cout << "lam_mu = " << lam_mu.ToString() << " (" << lam_mu.ToDouble() << ")\n";
    BigRat c_cone(18, 1000);
    BigRat margin = lam_mu * c_cone;
    std::cout << "margin = " << margin.ToString() << " (" << margin.ToDouble() << ")\n";
  } else {
    std::cout << "Signs do not match!\n";
  }
  return 0;
}
