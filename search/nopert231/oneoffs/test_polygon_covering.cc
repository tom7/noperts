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

  int chosen[] = {3054, 119, 3063, 22, 24};
  std::vector<vec3> v;
  for (int idx : chosen) {
    auto &ax = axes[idx];
    v.push_back(yocto::normalize(vec3{ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()}));
  }

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  BigVecQ3 u0 = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  double norm_u0 = std::sqrt((u0.x * u0.x + u0.y * u0.y + u0.z * u0.z).ToDouble());
  vec3 u0_hat = yocto::normalize(vec3{u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0_hat, std::abs(u0_hat.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0_hat, ex);

  double c_cone = 0.018;
  double cos_alpha = c_cone / norm_u0;
  double tan_alpha = std::sqrt(1.0 / (cos_alpha * cos_alpha) - 1.0);
  std::cout << "cos_alpha = " << cos_alpha << ", tan_alpha = " << tan_alpha << "\n";

  // Test circumscribed regular K-gons for K = 6, 8, 12, 16, 24
  for (int K : {6, 8, 12, 16, 20, 24, 32}) {
    // A circumscribed regular K-gon has side tangents at angles (2k)*pi/K
    // The vertices are at angles (2k+1)*pi/K with distance R_vert = tan_alpha / cos(pi/K)
    double R_vert = tan_alpha / std::cos(M_PI / K);
    std::vector<vec3> vertices;
    for (int k = 0; k < K; k++) {
      double phi = (2.0 * k + 1.0) * M_PI / K;
      vec3 vert = u0_hat + (R_vert * std::cos(phi)) * ex + (R_vert * std::sin(phi)) * ey;
      vertices.push_back(vert);
    }

    // Origin vertex O = u0_hat
    vec3 O = u0_hat;

    // For each wedge triangle T_k = conv(O, V_k, V_{k+1}), find best axis m
    bool all_covered = true;
    double min_wedge_margin = 1e9;
    std::vector<int> wedge_axis(K);

    for (int k = 0; k < K; k++) {
      int next_k = (k + 1) % K;
      vec3 V1 = vertices[k];
      vec3 V2 = vertices[next_k];

      int best_m = -1;
      double best_m_margin = -1e9;

      for (size_t m = 0; m < v.size(); m++) {
        // Because a . v_m = (a . u0_hat) * (p . v_m), the margin on unit sphere is:
        // dot(a, v_m) >= dot(p, v_m) / length(p) >= ...
        // More simply: for any p in T_k, p = u0_hat + x ex + y ey.
        // Its normalization is a = p / |p|.
        // At the 3 vertices O, V1, V2:
        double dot_O = yocto::dot(yocto::normalize(O), v[m]);
        double dot_V1 = yocto::dot(yocto::normalize(V1), v[m]);
        double dot_V2 = yocto::dot(yocto::normalize(V2), v[m]);

        double min_dot = std::min({dot_O, dot_V1, dot_V2});
        if (min_dot > best_m_margin) {
          best_m_margin = min_dot;
          best_m = m;
        }
      }

      if (best_m_margin < 0.003) {
        all_covered = false;
      }
      min_wedge_margin = std::min(min_wedge_margin, best_m_margin);
      wedge_axis[k] = best_m;
    }

    std::cout << "K = " << K << ": min wedge margin = " << min_wedge_margin;
    if (all_covered) {
      std::cout << " -> SUCCESS! All " << K << " wedges covered with margin >= 0.003!\n";
      std::cout << "Wedge axes: ";
      for (int k = 0; k < K; k++) std::cout << wedge_axis[k] << " ";
      std::cout << "\n";
      break;
    } else {
      std::cout << " (not yet covered)\n";
    }
  }
  return 0;
}
