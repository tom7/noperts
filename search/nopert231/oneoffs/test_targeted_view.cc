#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  vec3 axis = yocto::normalize(-u0);
  vec3 perp1 = yocto::normalize(yocto::cross(axis, vec3{1, 0, 0}));
  vec3 perp2 = yocto::cross(axis, perp1);

  double rad = 85.0 * M_PI / 180.0;
  double ca = std::cos(rad);
  double sa = std::sin(rad);

  vec3 ideal[3];
  for (int k = 0; k < 3; k++) {
    double phi = k * 2.0 * M_PI / 3.0;
    vec3 dir = axis * ca + (perp1 * std::cos(phi) + perp2 * std::sin(phi)) * sa;
    ideal[k] = yocto::normalize(dir);
    std::cout << "ideal[" << k << "] = (" << ideal[k].x << ", " << ideal[k].y << ", " << ideal[k].z << ")\n";
  }

  // For each ideal ray, find viewpoints on the great circle perpendicular to ideal[k]:
  for (int k = 0; k < 3; k++) {
    vec3 t1 = yocto::normalize(yocto::cross(ideal[k], vec3{0, 0, 1}));
    vec3 t2 = yocto::cross(ideal[k], t1);

    double max_dot = -1.0;
    int count = 0;
    for (double phi = 0; phi < 2 * M_PI; phi += 0.05) {
      vec3 v = t1 * std::cos(phi) + t2 * std::sin(phi);
      auto cands = Tube229::GenerateCandidatesForView(v, tri, true, 6, false);
      for (const auto &cand : cands) {
        ContactInfo c[3] = {cand.contacts[0], cand.contacts[1], cand.contacts[2]};
        AxisCertificate cert;
        BigVecQ3 ctr;
        BigRat del;
        if (Tube229::AuditAxis(tri, c, &cert, &ctr, &del, &err, BigRat(0))) {
          count++;
          vec3 u = {ctr.x.ToDouble() / cert.B.ToDouble(),
                    ctr.y.ToDouble() / cert.B.ToDouble(),
                    ctr.z.ToDouble() / cert.B.ToDouble()};
          double d = yocto::dot(yocto::normalize(u), ideal[k]);
          if (d > max_dot) max_dot = d;
        }
      }
    }
    std::cout << "Ideal " << k << ": audited " << count << " zero-defect axes, max dot with ideal = " << max_dot << "\n";
  }

  return 0;
}
