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

  int chosen[] = {3054, 119, 3063, 22, 24};
  std::vector<vec3> v;
  for (int idx : chosen) {
    auto &ax = axes[idx];
    ContactInfo cts[3] = {ax.cert.contacts[0], ax.cert.contacts[1], ax.cert.contacts[2]};
    AxisCertificate cert; BigVecQ3 ctr; BigRat del;
    Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
    v.push_back({ctr.x.ToDouble() / cert.B.ToDouble(),
                 ctr.y.ToDouble() / cert.B.ToDouble(),
                 ctr.z.ToDouble() / cert.B.ToDouble()});
  }

  double c_cone = 0.015;
  double c_core_target = 0.001;

  // Let n1 = ex, n2 = ey
  // Quadrants:
  // (s1, s2) in {(+1, +1), (+1, -1), (-1, +1), (-1, -1)}
  // For each quadrant, we need a flock axis v_m such that:
  // v_m = mu0 * u0 + mu1 * (s1 * n1) + mu2 * (s2 * n2)
  // with mu0, mu1, mu2 >= 0 and mu0 * c_cone >= c_core_target
  std::cout << "Testing coordinate cutting planes ex, ey:\n";
  int s1[4] = {1, 1, -1, -1};
  int s2[4] = {1, -1, 1, -1};

  for (int q = 0; q < 4; q++) {
    std::cout << "Quadrant (" << s1[q] << ", " << s2[q] << "):\n";
    vec3 ray1 = (float)s1[q] * ex;
    vec3 ray2 = (float)s2[q] * ey;

    // Check each axis v_m: can it be represented as mu0*u0 + mu1*ray1 + mu2*ray2?
    // In basis (u0, ray1, ray2):
    // Since u0 . ray1 = 0 and u0 . ray2 = 0, and ray1 . ray2 = 0:
    // mu0 = (v_m . u0) / |u0|^2
    // mu1 = v_m . ray1
    // mu2 = v_m . ray2
    bool q_ok = false;
    for (size_t m = 0; m < v.size(); m++) {
      double mu0 = yocto::dot(v[m], vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()}) / u0_sq.ToDouble();
      double mu1 = yocto::dot(v[m], ray1);
      double mu2 = yocto::dot(v[m], ray2);

      if (mu0 >= 0 && mu1 >= 0 && mu2 >= 0 && mu0 * c_cone >= c_core_target) {
        std::cout << "  Axis " << chosen[m] << ": mu0 = " << mu0 << ", mu1 = " << mu1 << ", mu2 = " << mu2
                  << " -> VALID! margin = " << (mu0 * c_cone) << "\n";
        q_ok = true;
      }
    }
    if (!q_ok) {
      std::cout << "  No axis in chosen 5 has mu >= 0 for this quadrant.\n";
    }
  }

  return 0;
}
