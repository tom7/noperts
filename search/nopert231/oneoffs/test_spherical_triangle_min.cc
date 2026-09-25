#include <iostream>
#include <cmath>
#include <algorithm>
#include <random>
#include "yocto-math.h"

using vec3 = yocto::vec<double, 3>;

int main() {
  std::mt19937_64 rng(42);
  std::uniform_real_distribution<double> dist(-1.0, 1.0);

  int failures = 0;
  int trials = 1000000;

  for (int t = 0; t < trials; t++) {
    // Generate an axis v
    vec3 v = yocto::normalize(vec3{dist(rng), dist(rng), dist(rng)});

    // Generate a reference center in the same hemisphere as v
    vec3 c = yocto::normalize(v + 0.5 * vec3{dist(rng), dist(rng), dist(rng)});

    // Generate 3 vertices near c (within 30 degrees)
    vec3 p[3];
    for (int i = 0; i < 3; i++) {
      vec3 pert = vec3{dist(rng), dist(rng), dist(rng)} * 0.4;
      p[i] = yocto::normalize(c + pert);
    }

    double min_vertex = std::min({yocto::dot(p[0], v), yocto::dot(p[1], v), yocto::dot(p[2], v)});
    if (min_vertex <= 0.001) continue; // Only test when vertices are positive

    // Sample 50 points inside the spherical triangle using positive barycentric coordinates
    for (int s = 0; s < 50; s++) {
      double w0 = std::abs(dist(rng));
      double w1 = std::abs(dist(rng));
      double w2 = std::abs(dist(rng));
      vec3 pt = yocto::normalize(w0 * p[0] + w1 * p[1] + w2 * p[2]);
      double dot_val = yocto::dot(pt, v);
      if (dot_val < min_vertex - 1e-12) {
        failures++;
        std::cout << "FAILURE! min_vertex = " << min_vertex << ", internal dot = " << dot_val << "\n";
        break;
      }
    }
    if (failures > 5) break;
  }

  std::cout << "Trials tested: " << trials << ", Failures: " << failures << "\n";
  return 0;
}
