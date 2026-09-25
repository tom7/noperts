#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // Complement cage axis ax0 (annular axis)
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0_raw = vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};
  double norm_u0 = yocto::length(u0_raw);
  vec3 u0 = yocto::normalize(u0_raw);
  vec3 k1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 k2 = yocto::cross(u0, k1);

  double c_cone = 0.017; // 17/1000
  double c_core = 0.000234013; // delta bound

  // In the cone: <a, u0_raw> >= c_cone.
  // Since ||u0_raw|| = norm_u0:
  // <a, u0> >= c_cone / norm_u0.
  double cos_alpha = c_cone / norm_u0;
  if (cos_alpha >= 1.0) {
    std::cout << "Cone is empty!\n";
    return 1;
  }
  double sin_alpha = std::sqrt(1.0 - cos_alpha * cos_alpha);
  double tan_alpha = sin_alpha / cos_alpha;
  std::cout << "norm_u0 = " << norm_u0 << "\n";
  std::cout << "cos_alpha = " << cos_alpha << " (alpha = " << std::acos(cos_alpha) * 180.0 / M_PI << " deg)\n";
  std::cout << "tan_alpha = " << tan_alpha << "\n";

  // We test circumscribed K-gon on plane <w, u0> = 1.
  // The circle has radius tan_alpha.
  // For a regular K-gon tangent to the circle, the vertices are at distance:
  // R_vertex = tan_alpha / cos(pi / K).
  // The rays are r_k = u0 + R_vertex * (cos(phi_k) k1 + sin(phi_k) k2).
  // And the center ray is r_center = u0.

  for (int K : {4, 6, 8, 12, 16, 24}) {
    double dphi = 2.0 * M_PI / K;
    double R_vertex = tan_alpha / std::cos(M_PI / K);

    std::vector<vec3> vertices;
    for (int k = 0; k < K; k++) {
      double phi = (k + 0.5) * dphi;
      vec3 r = u0 + R_vertex * (std::cos(phi) * k1 + std::sin(phi) * k2);
      vertices.push_back(r);
    }

    // Check if each sector (triangle formed by r_center, vertices[k], vertices[(k+1)%K])
    // can be covered by some axis v from our audited axes.
    // For a sector, the generators are: r_center, vertices[k], vertices[(k+1)%K].
    // An axis v covers the sector if for all 3 generators g:
    // dot(g, v_raw) >= c_core * ||g||.

    int covered_sectors = 0;
    std::vector<int> chosen_axes;

    for (int k = 0; k < K; k++) {
      vec3 g0 = u0; // center
      vec3 g1 = vertices[k];
      vec3 g2 = vertices[(k + 1) % K];
      double n0 = yocto::length(g0);
      double n1 = yocto::length(g1);
      double n2 = yocto::length(g2);

      int best_ax = -1;
      double best_margin = -1e9;

      for (size_t i = 0; i < axes.size(); i++) {
        ContactInfo cts[3] = {axes[i].cert.contacts[0], axes[i].cert.contacts[1], axes[i].cert.contacts[2]};
        AxisCertificate cert; BigVecQ3 ctr; BigRat del;
        Tube229::AuditAxis(tri, cts, &cert, &ctr, &del, &err, BigRat(0));
        vec3 v = vec3{ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()};

        double m0 = yocto::dot(g0, v) - c_core * n0;
        double m1 = yocto::dot(g1, v) - c_core * n1;
        double m2 = yocto::dot(g2, v) - c_core * n2;
        double min_m = std::min({m0, m1, m2});

        if (min_m > best_margin) {
          best_margin = min_m;
          best_ax = i;
        }
      }

      if (best_margin >= 0) {
        covered_sectors++;
        chosen_axes.push_back(best_ax);
      }
    }

    std::cout << "K = " << K << " regular circumscribed polygon: covered "
              << covered_sectors << " / " << K << " sectors.\n";
  }

  return 0;
}
