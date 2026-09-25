#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static BigRat DotQ(const BigVecQ3 &a, const BigVecQ3 &b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

static BigVecQ3 CrossQ(const BigVecQ3 &a, const BigVecQ3 &b) {
  return {a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
}

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
  BigVecQ3 u = ctr0;

  struct PosAxis {
    int idx;
    BigVecQ3 v;
    double dot_u;
  };
  std::vector<PosAxis> pos_axes;

  for (size_t i = 0; i < axes.size(); i++) {
    auto &ax = axes[i];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    BigRat d = DotQ(ctr, u);
    if (d > 0) {
      double d_dbl = d.ToDouble();
      pos_axes.push_back({(int)i, ctr, d_dbl});
    }
  }

  std::cout << "Found " << pos_axes.size() << " axes with positive dot product with u0!\n";

  // Check triples of positive axes:
  for (size_t i = 0; i < pos_axes.size(); i++) {
    for (size_t j = i + 1; j < pos_axes.size(); j++) {
      for (size_t k = j + 1; k < pos_axes.size(); k++) {
        BigVecQ3 v0 = pos_axes[i].v;
        BigVecQ3 v1 = pos_axes[j].v;
        BigVecQ3 v2 = pos_axes[k].v;

        BigVecQ3 c12 = CrossQ(v1, v2);
        BigRat det = DotQ(v0, c12);
        if (det <= 0) continue;

        BigRat l0 = DotQ(u, c12);
        if (l0 <= 0) continue;

        BigVecQ3 c20 = CrossQ(v2, v0);
        BigRat l1 = DotQ(u, c20);
        if (l1 <= 0) continue;

        BigVecQ3 c01 = CrossQ(v0, v1);
        BigRat l2 = DotQ(u, c01);
        if (l2 <= 0) continue;

        BigRat lam0 = l0 / det;
        BigRat lam1 = l1 / det;
        BigRat lam2 = l2 / det;
        BigRat sum_lam = lam0 + lam1 + lam2;

        std::cout << "FOUND STRICTLY POSITIVE ACUTE TRIPLE!\n";
        std::cout << "  Axes: " << pos_axes[i].idx << ", " << pos_axes[j].idx << ", " << pos_axes[k].idx << "\n";
        std::cout << "  lam0 = " << lam0.ToDouble() << ", lam1 = " << lam1.ToDouble() << ", lam2 = " << lam2.ToDouble() << "\n";
        std::cout << "  sum_lam = " << sum_lam.ToDouble() << "\n";
        return 0;
      }
    }
  }

  std::cout << "No strictly positive acute triple found.\n";
  return 0;
}
