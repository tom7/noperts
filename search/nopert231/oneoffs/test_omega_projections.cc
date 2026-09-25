#include <iostream>
#include <iomanip>
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
  // Corner 2 view of 031213002112122012121
  vec3 u = yocto::normalize(vec3{0.91602049, 0.20340275, 0.34573659});
  vec3 omega = yocto::normalize(vec3{-0.400992, 0.483041, 0.778381});

  TriangleQ tri = TriangleFromPath("031213002112122012121");
  ContactInfo sib0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate cert0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string fail0;
  bool ok0 = Tube229::AuditAxis(tri, sib0, &cert0, &center0, &delta0, &fail0, BigRat(1, 1000));
  if (!ok0) {
    std::cout << "AuditAxis failed: " << fail0 << "\n";
    return 1;
  }
  vec3 c0 = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};
  vec3 c0_norm = yocto::normalize(c0);
  std::cout << "Axis 0 center: (" << c0.x << ", " << c0.y << ", " << c0.z << ") norm=" << yocto::length(c0) << "\n";
  std::cout << "Axis 0 normalized center: (" << c0_norm.x << ", " << c0_norm.y << ", " << c0_norm.z << ")\n";

  auto cands_hull = Tube229::GenerateCandidatesForView(u, tri, false);
  double max_dot_hull = -1e9;
  int best_h = -1;
  for (size_t i = 0; i < cands_hull.size(); i++) {
    double d = yocto::dot(c0_norm, cands_hull[i].normalized_a);
    if (d > max_dot_hull) {
      max_dot_hull = d;
      best_h = i;
    }
  }
  std::cout << "Max dot of Axis 0 with any 9-hull candidate: " << max_dot_hull << "\n";
  if (best_h >= 0) {
    const auto &bh = cands_hull[best_h];
    std::cout << "Best hull axis contacts: ("
              << bh.contacts[0].vertex << ", "
              << bh.contacts[1].vertex << ", "
              << bh.contacts[2].vertex << ")\n";
    std::cout << "Normalized vector: (" << bh.normalized_a.x << ", "
              << bh.normalized_a.y << ", " << bh.normalized_a.z << ")\n";
  }

  return 0;
}
