#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});

  std::vector<std::pair<double, int>> ranked;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000200) {
      vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
      double d = yocto::dot(u0, v);
      ranked.push_back({d, (int)i});
    }
  }

  std::sort(ranked.rbegin(), ranked.rend());
  std::cout << "Top 15 axes pointing towards u0 (with delta <= 0.000200):\n";
  for (int i = 0; i < std::min((int)ranked.size(), 15); i++) {
    int idx = ranked[i].second;
    double B = axes[idx].cert.B.ToDouble();
    vec3 v = vec3{axes[idx].center.x.ToDouble() / B, axes[idx].center.y.ToDouble() / B, axes[idx].center.z.ToDouble() / B};
    std::cout << "Rank " << i << ": Axis " << idx << ", dot = " << ranked[i].first
              << ", len(center/B) = " << yocto::length(v)
              << ", delta = " << axes[idx].delta.ToDouble()
              << ", B = " << B << "\n";
  }
  return 0;
}
