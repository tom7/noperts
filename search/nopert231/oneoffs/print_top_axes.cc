#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  vec3 a = yocto::normalize(vec3{0.3992, -0.4799, -0.7813});
  double box_delta = 165676.0 / 1000000000.0;

  struct Hit {
    double dot;
    double delta;
    int idx;
  };
  std::vector<Hit> hits;

  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      hits.push_back({yocto::dot(a, v), ax.delta.ToDouble(), (int)i});
    }
  }

  std::sort(hits.begin(), hits.end(), [](const Hit &x, const Hit &y) {
    return x.dot > y.dot;
  });

  std::cout << "Top 10 axes at a:\n";
  for (int i = 0; i < 10 && i < hits.size(); i++) {
    std::cout << "#" << i << ": idx " << hits[i].idx << ", dot = " << hits[i].dot
              << ", delta = " << hits[i].delta << "\n";
  }
  return 0;
}
