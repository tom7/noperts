#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 100);
  std::cout << "Loaded " << axes.size() << " axes.\n";

  // Identify all axes with dot(u, u0) > 0.1
  ContactInfo c0[3] = {
    ContactInfo{3, 2, 2, 1, 800, 2},
    ContactInfo{1, 4, 4, 8, 800, 4},
    ContactInfo{13, 14, 14, 15, 200, 14}
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = yocto::normalize(ToVec3(ctr0));

  std::vector<int> pos_axes, neg_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 u = yocto::normalize(ToVec3(axes[i].center));
    if (yocto::dot(u, u0) > 0.1) pos_axes.push_back(i);
    else neg_axes.push_back(i);
  }
  std::cout << "Positive axes: " << pos_axes.size() << ", Negative axes: " << neg_axes.size() << "\n";

  // Test cages: 1 positive axis + 3 negative axes
  for (int p_idx : pos_axes) {
    vec3 c0 = ToVec3(axes[p_idx].center);
    int M = neg_axes.size();
    for (int j1 = 0; j1 < M; j1++) {
      vec3 c1 = ToVec3(axes[neg_axes[j1]].center);
      for (int j2 = j1 + 1; j2 < M; j2++) {
        vec3 c2 = ToVec3(axes[neg_axes[j2]].center);
        for (int j3 = j2 + 1; j3 < M; j3++) {
          vec3 c3 = ToVec3(axes[neg_axes[j3]].center);

          double V0 = yocto::dot(c1, yocto::cross(c2, c3));
          double V1 = -yocto::dot(c0, yocto::cross(c2, c3));
          double V2 = yocto::dot(c0, yocto::cross(c1, c3));
          double V3 = -yocto::dot(c0, yocto::cross(c1, c2));

          double total = V0 + V1 + V2 + V3;
          if (std::abs(total) < 1e-9) continue;

          double l0 = V0 / total;
          double l1 = V1 / total;
          double l2 = V2 / total;
          double l3 = V3 / total;

          if (l0 > 0.01 && l1 > 0.01 && l2 > 0.01 && l3 > 0.01) {
            std::cout << "FOUND PURE ZERO-DEFECT CAGE! ("
                      << p_idx << ", " << neg_axes[j1] << ", " << neg_axes[j2] << ", " << neg_axes[j3] << ")\n";
            std::cout << "Lambdas: " << l0 << ", " << l1 << ", " << l2 << ", " << l3 << "\n";

            // Now check if it satisfies full TubeCertificate audit:
            TubeCertificate cert;
            cert.axes[0] = axes[p_idx].cert;
            cert.axes[1] = axes[neg_axes[j1]].cert;
            cert.axes[2] = axes[neg_axes[j2]].cert;
            cert.axes[3] = axes[neg_axes[j3]].cert;
            cert.c = BigRat(1, 4000);
            cert.delta = del0;
            cert.r = BigRat(1, 300);

            TubeCertificate out_cert;
            std::string fail_reason;
            if (Tube229::AuditCertificateAdaptive(tri, cert, &out_cert, &fail_reason)) {
              std::cout << "PURE ZERO-DEFECT TUBE CERTIFICATE AUDIT PASSED!\n";
              std::cout << "c = " << out_cert.c.ToDouble() << ", delta = " << out_cert.delta.ToDouble() << "\n";
              return 0;
            } else {
              std::cout << "Audit failed: " << fail_reason << "\n";
            }
          }
        }
      }
    }
  }

  std::cout << "No pure cage found among tested combinations.\n";
  return 0;
}
