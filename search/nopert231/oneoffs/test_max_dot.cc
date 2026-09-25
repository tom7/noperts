#include <iostream>
#include <vector>
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
  u0 = yocto::normalize(u0);

  auto all_axes = Tube229::FindAllHullSupportAxes(tri, 500);
  double max_dot = -1.0;
  int best_idx = -1;
  for (size_t i = 0; i < all_axes.size(); i++) {
    vec3 u = {all_axes[i].center.x.ToDouble() / all_axes[i].cert.B.ToDouble(),
              all_axes[i].center.y.ToDouble() / all_axes[i].cert.B.ToDouble(),
              all_axes[i].center.z.ToDouble() / all_axes[i].cert.B.ToDouble()};
    u = yocto::normalize(u);
    double d = yocto::dot(u, u0);
    if (d > max_dot) {
      max_dot = d;
      best_idx = i;
    }
  }

  std::cout << "Among " << all_axes.size() << " zero-defect axes:\n";
  std::cout << "Maximum dot product with u0 is: " << max_dot << " (axis " << best_idx << ")\n";
  return 0;
}
