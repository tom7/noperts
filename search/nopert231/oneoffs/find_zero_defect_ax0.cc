#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  // Target ax0 direction:
  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  double B0 = ax0.B.ToDouble();
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0});

  std::cout << "Target u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";

  // Find pure hull axes closest to u0:
  std::vector<std::pair<double, int>> ranked;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000200) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B});
      double d = yocto::dot(u0, v);
      ranked.push_back({d, (int)i});
    }
  }
  std::sort(ranked.rbegin(), ranked.rend());

  for (int i = 0; i < 10; i++) {
    int idx = ranked[i].second;
    std::cout << "Rank " << i << ": Axis " << idx << ", dot = " << ranked[i].first
              << ", delta = " << axes[idx].delta.ToDouble()
              << ", B = " << axes[idx].cert.B.ToDouble() << "\n";
  }

  return 0;
}
