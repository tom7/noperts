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
  std::cout << "Finding hull support axes for " << path << "...\n";
  auto axes = Tube229::FindAllHullSupportAxes(tri, 300);
  std::cout << "Found " << axes.size() << " zero-defect axes.\n";

  int N = axes.size();
  int found = 0;
  double max_min_lambda = 0;
  for (int i0 = 0; i0 < N; i0++) {
    vec3 c0 = ToVec3(axes[i0].center);
    for (int i1 = i0 + 1; i1 < N; i1++) {
      vec3 c1 = ToVec3(axes[i1].center);
      for (int i2 = i1 + 1; i2 < N; i2++) {
        vec3 c2 = ToVec3(axes[i2].center);
        for (int i3 = i2 + 1; i3 < N; i3++) {
          vec3 c3 = ToVec3(axes[i3].center);

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

          if (l0 > 1e-4 && l1 > 1e-4 && l2 > 1e-4 && l3 > 1e-4) {
            found++;
            double m = std::min({l0, l1, l2, l3});
            if (m > max_min_lambda) {
              max_min_lambda = m;
              std::cout << "New best cage: min lambda = " << m
                        << " (l0=" << l0 << ", l1=" << l1 << ", l2=" << l2 << ", l3=" << l3 << ")"
                        << " indices: " << i0 << ", " << i1 << ", " << i2 << ", " << i3 << "\n";

              TubeCertificate test_cert;
              test_cert.axes[0] = axes[i0].cert;
              test_cert.axes[1] = axes[i1].cert;
              test_cert.axes[2] = axes[i2].cert;
              test_cert.axes[3] = axes[i3].cert;

              TubeCertificate verified;
              std::string fail;
              if (Tube229::AuditCertificateAdaptive(tri, test_cert, &verified, &fail)) {
                std::cout << "  AUDIT SUCCESS! c = " << verified.c.ToString()
                          << " (" << verified.c.ToDouble() << "), r = "
                          << verified.r.ToString() << " (" << verified.r.ToDouble() << ")\n";
                return 0;
              } else {
                std::cout << "  Audit failed: " << fail << "\n";
              }
            }
          }
        }
      }
    }
  }

  std::cout << "Total cages with positive lambda: " << found << "\n";
  return 0;
}
