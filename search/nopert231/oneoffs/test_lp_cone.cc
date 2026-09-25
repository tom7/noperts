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

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});

  std::vector<vec3> V;
  std::vector<int> orig_idx;
  for (size_t i = 0; i < axes.size(); i++) {
    auto &ax = axes[i];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    vec3 v = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    double d = yocto::dot(u0, v);
    if (d > 0.0) { // acute or in forward hemisphere
      V.push_back(v);
      orig_idx.push_back(i);
    }
  }

  std::cout << "Number of forward-hemisphere axes: " << V.size() << "\n";

  // Check all quadruples of forward-hemisphere axes:
  // Is u0 in the convex cone of any 3 or 4 forward-hemisphere axes?
  // u0 = sum mu_i v_i with mu_i > 0
  int found3 = 0;
  for (size_t i = 0; i < V.size(); i++) {
    for (size_t j = i + 1; j < V.size(); j++) {
      for (size_t k = j + 1; k < V.size(); k++) {
        vec3 c12 = yocto::cross(V[j], V[k]);
        double det = yocto::dot(V[i], c12);
        if (std::abs(det) < 1e-5) continue;
        double l0 = yocto::dot(u0, c12) / det;
        double l1 = yocto::dot(u0, yocto::cross(V[k], V[i])) / det;
        double l2 = yocto::dot(u0, yocto::cross(V[i], V[j])) / det;
        if (l0 > 0 && l1 > 0 && l2 > 0) {
          found3++;
          std::cout << "FOUND 3-AXIS POSITIVE COMBINATION in forward hemisphere!\n";
          std::cout << "  Axes: " << orig_idx[i] << ", " << orig_idx[j] << ", " << orig_idx[k] << "\n";
          std::cout << "  dots with u0: " << yocto::dot(u0, V[i]) << ", " << yocto::dot(u0, V[j]) << ", " << yocto::dot(u0, V[k]) << "\n";
          std::cout << "  l0=" << l0 << ", l1=" << l1 << ", l2=" << l2 << ", sum=" << l0+l1+l2 << "\n";
          return 0;
        }
      }
    }
  }

  std::cout << "No 3-axis positive combination found in forward hemisphere.\n";
  return 0;
}
