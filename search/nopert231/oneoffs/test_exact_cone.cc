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

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  // The 3 axes: 3063, 22, 24
  int idxs[3] = {3063, 22, 24};
  BigVecQ3 v[3];
  for (int i = 0; i < 3; i++) {
    auto &ax = axes[idxs[i]];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v[i] = ctr;
  }

  // Solve ctr0 = lam[0]*v[0] + lam[1]*v[1] + lam[2]*v[2] in exact rationals:
  // Determinant:
  auto cross = [](const BigVecQ3 &a, const BigVecQ3 &b) {
    return BigVecQ3{a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
  };
  auto dot = [](const BigVecQ3 &a, const BigVecQ3 &b) {
    return a.x * b.x + a.y * b.y + a.z * b.z;
  };

  BigVecQ3 c12 = cross(v[1], v[2]);
  BigRat det = dot(v[0], c12);

  BigRat lam0 = dot(ctr0, c12) / det;
  BigRat lam1 = dot(ctr0, cross(v[2], v[0])) / det;
  BigRat lam2 = dot(ctr0, cross(v[0], v[1])) / det;

  std::cout << "det = " << det.ToString() << " (" << det.ToDouble() << ")\n";
  std::cout << "lam0 = " << lam0.ToString() << " (" << lam0.ToDouble() << ")\n";
  std::cout << "lam1 = " << lam1.ToString() << " (" << lam1.ToDouble() << ")\n";
  std::cout << "lam2 = " << lam2.ToString() << " (" << lam2.ToDouble() << ")\n";

  // Check equality:
  BigVecQ3 sum = {
    lam0 * v[0].x + lam1 * v[1].x + lam2 * v[2].x,
    lam0 * v[0].y + lam1 * v[1].y + lam2 * v[2].y,
    lam0 * v[0].z + lam1 * v[1].z + lam2 * v[2].z
  };

  bool ok = (sum.x == ctr0.x && sum.y == ctr0.y && sum.z == ctr0.z);
  std::cout << "Exact match: " << (ok ? "YES!" : "NO") << "\n";

  return 0;
}
