#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0 = yocto::length(u0);

  auto axes = Tube229::FindAllHullSupportAxes(tri, 10000);
  std::cout << "Found " << axes.size() << " zero-defect axes.\n";

  struct Cand {
    int idx;
    double angle;
    double norm;
    double cos_ang;
  };
  std::vector<Cand> cands;

  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double cos_a = yocto::dot(u0, v) / (norm_u0 * yocto::length(v));
    if (cos_a > -1.0 && cos_a < 1.0) {
      double ang = std::acos(cos_a) * 180.0 / M_PI;
      cands.push_back({(int)i, ang, yocto::length(v), cos_a});
    }
  }

  std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
    return a.angle < b.angle;
  });

  std::cout << "Top 10 closest zero-defect axes to u0:\n";
  for (int i = 0; i < std::min(10, (int)cands.size()); i++) {
    const auto &c = cands[i];
    const auto &ax = axes[c.idx].cert;
    std::cout << i << ": angle = " << c.angle << " deg, norm = " << c.norm
              << ", B = " << ax.B.ToDouble()
              << ", contacts: (" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << ")\n";
  }

  return 0;
}
