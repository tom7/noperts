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
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert; BigVecQ3 ann_center; BigRat ann_del; std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = {ann_center.x.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.y.ToDouble() / ann_cert.B.ToDouble(),
             ann_center.z.ToDouble() / ann_cert.B.ToDouble()};
  vec3 dir_u0 = yocto::normalize(u0);

  struct Cand {
    size_t idx;
    double dot;
    double norm;
    vec3 v;
  };
  std::vector<Cand> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = {axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
              axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(yocto::normalize(v), dir_u0);
    cands.push_back({i, d, yocto::length(v), v});
  }

  std::sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
    return a.dot > b.dot;
  });

  std::cout << "Top 15 closest axes in FindAllHullSupportAxes:\n";
  for (int i = 0; i < 15; i++) {
    size_t idx = cands[i].idx;
    const auto &ax = axes[idx];
    std::cout << "#" << i << " (idx " << idx << "): dot=" << cands[i].dot
              << ", angle=" << (std::acos(std::clamp(cands[i].dot, -1.0, 1.0)) * 180.0 / M_PI) << " deg"
              << ", norm=" << cands[i].norm
              << ", B=" << ax.cert.B.ToDouble() << "\n";
    for (int c = 0; c < 3; c++) {
      const auto &ci = ax.cert.contacts[c];
      std::cout << "   c" << c << ": (" << ci.edge_start << "->" << ci.edge_finish << ", "
                << ci.edge_start2 << "->" << ci.edge_finish2 << ", mix=" << ci.mix << ", v=" << ci.vertex << ")\n";
    }
  }
  return 0;
}
