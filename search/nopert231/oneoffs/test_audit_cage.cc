#include <iostream>
#include <vector>
#include "bignum/big-overloads.h"
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

bool TryCertifyPath(const std::string &path) {
  TriangleQ tri = TriangleFromPath(path);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 200);

  int N = axes.size();
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
          if (std::abs(total) < 1e-6) continue;

          double l0 = V0 / total;
          double l1 = V1 / total;
          double l2 = V2 / total;
          double l3 = V3 / total;

          if (l0 > 0.05 && l1 > 0.05 && l2 > 0.05 && l3 > 0.05) {
            TubeCertificate test_cert;
            test_cert.axes[0] = axes[i0].cert;
            test_cert.axes[1] = axes[i1].cert;
            test_cert.axes[2] = axes[i2].cert;
            test_cert.axes[3] = axes[i3].cert;

            TubeCertificate out_cert;
            std::string fail;
            if (Tube229::AuditCertificateAdaptive(tri, test_cert, &out_cert, &fail)) {
              std::cout << "SUCCESS on " << path << ": c=" << out_cert.c.ToDouble()
                        << ", r=" << out_cert.r.ToDouble() << "\n";
              return true;
            }
          }
        }
      }
    }
  }

  std::cout << "FAIL on " << path << "\n";
  return false;
}

int main() {
  std::vector<std::string> paths = {
    "3121303021",
    "3121303022",
    "3121303023",
    "3121303200",
    "312130332",
    // Also test children of 3121300:
    "31213000",
    "31213001",
    "31213002",
    "31213003",
  };

  for (const auto &p : paths) {
    TryCertifyPath(p);
  }

  return 0;
}
