#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()};

  std::cout << "Audited " << axes.size() << " axes. Finding 3 axes to cage u0 with max c_cone...\n";

  // For each triple of axes (j1, j2, j3), check if u0 is in their cone:
  // i.e., u0 = - (mu1 * v1 + mu2 * v2 + mu3 * v3) with mu_i > 0
  // If so, (u0, v1, v2, v3) forms a simplex enclosing the origin!
  double best_c_cone = 0.0;
  int best_j1 = -1, best_j2 = -1, best_j3 = -1;

  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v1 = vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()};
    for (size_t j = i + 1; j < axes.size(); j++) {
      vec3 v2 = vec3{axes[j].center.x.ToDouble(), axes[j].center.y.ToDouble(), axes[j].center.z.ToDouble()};
      for (size_t k = j + 1; k < axes.size(); k++) {
        vec3 v3 = vec3{axes[k].center.x.ToDouble(), axes[k].center.y.ToDouble(), axes[k].center.z.ToDouble()};

        // Det of (v1, v2, v3)
        double det = yocto::dot(v1, yocto::cross(v2, v3));
        if (std::abs(det) < 1e-6) continue;

        // Express -u0 as linear combo of v1, v2, v3: -u0 = mu1 v1 + mu2 v2 + mu3 v3
        double mu1 = yocto::dot(-u0, yocto::cross(v2, v3)) / det;
        double mu2 = yocto::dot(v1, yocto::cross(-u0, v3)) / det;
        double mu3 = yocto::dot(v1, yocto::cross(v2, -u0)) / det;

        if (mu1 > 0 && mu2 > 0 && mu3 > 0) {
          // They enclose the origin!
          // Now compute the inradius c of the simplex (u0_scaled, v1, v2, v3)
          // For a target c = 0.0005, what is the maximum c_cone?
          // Since scaling u0 by factor S = (c + delta)/c_cone contracts u0 towards 0,
          // larger S means larger c_cone!
          // S = min over 4 facets of normal distance to facet.
          // In particular, the distance from 0 to the facet (v1, v2, v3) is the max possible inradius.
          vec3 n = yocto::normalize(yocto::cross(v2 - v1, v3 - v1));
          double d0 = std::abs(yocto::dot(v1, n));
          if (d0 > best_c_cone) {
            best_c_cone = d0;
            best_j1 = i; best_j2 = j; best_j3 = k;
          }
        }
      }
    }
  }

  std::cout << "Best facet distance d0: " << best_c_cone << "\n";
  if (best_j1 >= 0) {
    std::cout << "Indices: (" << best_j1 << ", " << best_j2 << ", " << best_j3 << ")\n";
  } else {
    std::cout << "NO TRIPLE ENCLOSES -u0!\n";
  }

  return 0;
}
