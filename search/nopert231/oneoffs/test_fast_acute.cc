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
  vec3 u_dbl = yocto::normalize(vec3{u.x.ToDouble(), u.y.ToDouble(), u.z.ToDouble()});

  struct PosAxis {
    int idx;
    BigVecQ3 v_big;
    vec3 v_dbl;
    double dot_u;
  };
  std::vector<PosAxis> pos_axes;

  for (size_t i = 0; i < axes.size(); i++) {
    auto &ax = axes[i];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    vec3 v_norm = yocto::normalize(vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    double d = yocto::dot(v_norm, u_dbl);
    if (d > 0.4) {
      pos_axes.push_back({(int)i, ctr, v_norm, d});
    }
  }

  std::cout << "Filtered to " << pos_axes.size() << " axes with dot(u, v) > 0.4\n";

  // Double search
  for (size_t i = 0; i < pos_axes.size(); i++) {
    for (size_t j = i + 1; j < pos_axes.size(); j++) {
      for (size_t k = j + 1; k < pos_axes.size(); k++) {
        vec3 v0 = pos_axes[i].v_dbl;
        vec3 v1 = pos_axes[j].v_dbl;
        vec3 v2 = pos_axes[k].v_dbl;

        vec3 c12 = yocto::cross(v1, v2);
        double det = yocto::dot(v0, c12);
        if (std::abs(det) < 1e-4) continue;

        double l0 = yocto::dot(u_dbl, c12) / det;
        if (l0 <= 0.05) continue;

        vec3 c20 = yocto::cross(v2, v0);
        double l1 = yocto::dot(u_dbl, c20) / det;
        if (l1 <= 0.05) continue;

        vec3 c01 = yocto::cross(v0, v1);
        double l2 = yocto::dot(u_dbl, c01) / det;
        if (l2 <= 0.05) continue;

        std::cout << "FOUND CANDIDATE in double!\n";
        std::cout << "  Axes: " << pos_axes[i].idx << ", " << pos_axes[j].idx << ", " << pos_axes[k].idx << "\n";
        std::cout << "  l0=" << l0 << ", l1=" << l1 << ", l2=" << l2 << "\n";
        std::cout << "  sum_l = " << l0 + l1 + l2 << "\n";

        // Verify with BigRat:
        BigVecQ3 V0 = pos_axes[i].v_big;
        BigVecQ3 V1 = pos_axes[j].v_big;
        BigVecQ3 V2 = pos_axes[k].v_big;
        BigVecQ3 C12 = CrossQ(V1, V2);
        BigRat Det = DotQ(V0, C12);
        BigRat L0 = DotQ(u, C12) / Det;
        BigRat L1 = DotQ(u, CrossQ(V2, V0)) / Det;
        BigRat L2 = DotQ(u, CrossQ(V0, V1)) / Det;
        std::cout << "  BigRat: L0=" << L0.ToDouble() << ", L1=" << L1.ToDouble() << ", L2=" << L2.ToDouble() << "\n";
        if (L0 > 0 && L1 > 0 && L2 > 0) {
          std::cout << "  SUCCESS! ALL L > 0 in BigRat!\n";
          return 0;
        }
      }
    }
  }

  std::cout << "None found with dot > 0.4\n";
  return 0;
}
