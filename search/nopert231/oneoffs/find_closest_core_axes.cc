#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  vec3 u0 = {-0.01389, 0.01857, -0.06689};
  vec3 u0_hat = yocto::normalize(u0);

  struct Cand {
    int idx;
    double dot;
    double deg;
  };
  std::vector<Cand> cands;

  for (size_t i = 0; i < base_axes.size(); i++) {
    vec3 a = yocto::normalize(ToDouble(base_axes[i].center));
    double d = yocto::dot(a, u0_hat);
    if (d > 0.5) { // within 60 degrees
      double deg = acos(std::min(1.0, std::max(-1.0, d))) * 180.0 / M_PI;
      cands.push_back({(int)i, d, deg});
    }
  }

  std::sort(cands.begin(), cands.end(), [](const Cand &x, const Cand &y) {
    return x.dot > y.dot;
  });

  std::cout << "Found " << cands.size() << " axes within 60 degrees of u0:\n";
  for (size_t i = 0; i < std::min((size_t)20, cands.size()); i++) {
    std::cout << "  idx " << cands[i].idx << ": dot = " << cands[i].dot << " (" << cands[i].deg << " deg)\n";
  }
  return 0;
}
