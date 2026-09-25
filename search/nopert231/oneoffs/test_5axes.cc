#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  int chosen[4] = {0, 24, 210, 424};
  std::vector<vec3> u;
  u.push_back(u0);
  for (int idx : chosen) {
    u.push_back(vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                     axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                     axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()});
  }

  // Check if origin is strictly in convex hull of u[0..4]:
  // There exist lambda_0..4 > 0 summing to 1 such that sum lambda_i u_i = 0.
  // Test all subsets of 4 of the 5 vectors:
  for (int omit = 0; omit < 5; omit++) {
    std::vector<vec3> sub;
    for (int i = 0; i < 5; i++) if (i != omit) sub.push_back(u[i]);
    vec3 c0 = sub[0], c1 = sub[1], c2 = sub[2], c3 = sub[3];
    double V0 = yocto::dot(c1, yocto::cross(c2, c3));
    double V1 = -yocto::dot(c0, yocto::cross(c2, c3));
    double V2 = yocto::dot(c0, yocto::cross(c1, c3));
    double V3 = -yocto::dot(c0, yocto::cross(c1, c2));
    double total = V0 + V1 + V2 + V3;
    if (std::abs(total) < 1e-9) continue;
    double l0 = V0 / total, l1 = V1 / total, l2 = V2 / total, l3 = V3 / total;
    if (l0 > 1e-5 && l1 > 1e-5 && l2 > 1e-5 && l3 > 1e-5) {
      std::cout << "Subset omitting " << omit << " cages origin! ("
                << l0 << ", " << l1 << ", " << l2 << ", " << l3 << ")\n";
    }
  }

  return 0;
}
