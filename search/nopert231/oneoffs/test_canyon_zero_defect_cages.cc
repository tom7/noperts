#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0 = MakeContact(3, 2, 2, 1, 800, 2);
  ContactInfo c1 = MakeContact(1, 4, 4, 8, 800, 4);

  struct Cand {
    ContactInfo contacts[3];
    AxisCertificate cert;
    BigVecQ3 center;
    BigRat delta;
    vec3 c_f;
  };
  std::vector<Cand> cands;

  // 1. All zero defect axes with c0, c1:
  std::string err;
  for (int v2 = 0; v2 < 20; v2++) {
    for (int v1 = 0; v1 < 20; v1++) {
      if (v1 == v2) continue;
      for (int v3 = 0; v3 < 20; v3++) {
        if (v3 == v2 || v3 == v1) continue;
        for (int mix : {0, 200, 400, 600, 800, 1000}) {
          ContactInfo test_c[3] = {c0, c1, MakeContact(v1, v2, v2, v3, mix, v2)};
          AxisCertificate ax;
          BigVecQ3 ctr;
          BigRat del;
          if (Tube229::AuditAxis(tri, test_c, &ax, &ctr, &del, &err, BigRat(0))) {
            cands.push_back({
              {test_c[0], test_c[1], test_c[2]},
              ax, ctr, del, ToVec3(ctr)
            });
          }
        }
      }
    }
  }

  // 2. The 3 known complement axes:
  ContactInfo comp[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  for (int i = 0; i < 3; i++) {
    AxisCertificate ax;
    BigVecQ3 ctr;
    BigRat del;
    if (Tube229::AuditAxis(tri, comp[i], &ax, &ctr, &del, &err, BigRat(0))) {
      cands.push_back({
        {comp[i][0], comp[i][1], comp[i][2]},
        ax, ctr, del, ToVec3(ctr)
      });
    }
  }

  std::cout << "Testing cages among " << cands.size() << " candidates...\n";
  int N = cands.size();
  int found = 0;
  for (int i0 = 0; i0 < N; i0++) {
    vec3 v0 = cands[i0].c_f;
    for (int i1 = i0 + 1; i1 < N; i1++) {
      vec3 v1 = cands[i1].c_f;
      for (int i2 = i1 + 1; i2 < N; i2++) {
        vec3 v2 = cands[i2].c_f;
        for (int i3 = i2 + 1; i3 < N; i3++) {
          vec3 v3 = cands[i3].c_f;

          double V0 = yocto::dot(v1, yocto::cross(v2, v3));
          double V1 = -yocto::dot(v0, yocto::cross(v2, v3));
          double V2 = yocto::dot(v0, yocto::cross(v1, v3));
          double V3 = -yocto::dot(v0, yocto::cross(v1, v2));

          double total = V0 + V1 + V2 + V3;
          if (std::abs(total) < 1e-6) continue;

          double l0 = V0 / total;
          double l1 = V1 / total;
          double l2 = V2 / total;
          double l3 = V3 / total;

          if (l0 > 0.01 && l1 > 0.01 && l2 > 0.01 && l3 > 0.01) {
            TubeCertificate test_cert;
            test_cert.axes[0] = cands[i0].cert;
            test_cert.axes[1] = cands[i1].cert;
            test_cert.axes[2] = cands[i2].cert;
            test_cert.axes[3] = cands[i3].cert;

            TubeCertificate verified_cert;
            std::string fail;
            if (Tube229::AuditCertificateAdaptive(tri, test_cert, &verified_cert, &fail)) {
              std::cout << "FOUND CAGE CERT! c=" << verified_cert.c.ToDouble()
                        << " r=" << verified_cert.r.ToDouble() << "\n";
              found++;
              if (found >= 5) return 0;
            }
          }
        }
      }
    }
  }

  std::cout << "Finished search, found " << found << " cages.\n";
  return 0;
}
