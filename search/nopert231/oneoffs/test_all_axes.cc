#include <iostream>
#include <vector>
#include <algorithm>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  vec3 omega_obs = {-0.400992, 0.483041, 0.778381};
  vec3 neg_omega = -omega_obs;

  std::vector<std::string> paths = {
    "3121300",
    "3121303021",
    "31213030211",
    "312130302112",
    "3121303021121",
    "31213030211212",
  };

  for (const auto &path : paths) {
    TriangleQ tri = TriangleFromPath(path);
    auto axes = Tube229::FindAllHullSupportAxes(tri, 200);

    // Find best axis pointing towards -omega:
    double best_dot = -1.0;
    int best_idx = -1;
    for (size_t i = 0; i < axes.size(); i++) {
      vec3 u = yocto::normalize(ToVec3(axes[i].center));
      double d = yocto::dot(u, neg_omega);
      if (d > best_dot) {
        best_dot = d;
        best_idx = i;
      }
    }

    std::cout << "Path " << path << " (depth " << path.size() << "): "
              << axes.size() << " axes, best dot(-omega) = " << best_dot;
    if (best_idx >= 0) {
      std::cout << " contacts: ("
                << axes[best_idx].cert.contacts[0].vertex << ", "
                << axes[best_idx].cert.contacts[1].vertex << ", "
                << axes[best_idx].cert.contacts[2].vertex << ")\n";
    } else {
      std::cout << "\n";
    }
  }

  return 0;
}
