#include <iostream>
#include <vector>
#include <random>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static bool InTetrahedron(const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3, const vec3 &p, double margin = 0.0) {
  vec3 d0 = v0 - v3;
  vec3 d1 = v1 - v3;
  vec3 d2 = v2 - v3;
  double d = Det3(d0, d1, d2);
  if (fabs(d) < 1e-12) return false;

  vec3 dp = p - v3;
  double b0 = Det3(dp, d1, d2) / d;
  double b1 = Det3(d0, dp, d2) / d;
  double b2 = Det3(d0, d1, dp) / d;
  double b3 = 1.0 - b0 - b1 - b2;

  return (b0 >= margin && b1 >= margin && b2 >= margin && b3 >= margin);
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Candidate pool size: " << base_axes.size() << "\n";

  vec3 u0 = {-0.01389, 0.01857, -0.06689};
  double c_cone = 0.038;
  double c = 0.00001; // 1/100000
  double delta = 4e-7;
  double scale = (c + delta) / c_cone;
  vec3 v0 = scale * u0;

  double R_target = 1.75 * (c + delta);
  vec3 targets[6] = {
    {+R_target, 0, 0},
    {-R_target, 0, 0},
    {0, +R_target, 0},
    {0, -R_target, 0},
    {0, 0, +R_target},
    {0, 0, -R_target}
  };

  std::vector<vec3> centers(base_axes.size());
  for (size_t i = 0; i < base_axes.size(); i++) {
    centers[i] = ToDouble(base_axes[i].center);
  }

  std::cout << "Searching for winning 3-axis complement cage...\n";
  int found = 0;

  std::mt19937 rng(42);
  std::uniform_int_distribution<size_t> dist(0, base_axes.size() - 1);

  for (int iter = 0; iter < 10000000; iter++) {
    size_t i1 = dist(rng);
    size_t i2 = dist(rng);
    size_t i3 = dist(rng);
    if (i1 == i2 || i2 == i3 || i1 == i3) continue;

    const vec3 &v1 = centers[i1];
    const vec3 &v2 = centers[i2];
    const vec3 &v3 = centers[i3];

    bool all_in = true;
    for (int k = 0; k < 6; k++) {
      if (!InTetrahedron(v0, v1, v2, v3, targets[k], 1e-6)) {
        all_in = false;
        break;
      }
    }

    if (all_in) {
      std::cout << "FOUND WINNING CAGE! indices: " << i1 << ", " << i2 << ", " << i3 << "\n";
      found++;
      if (found >= 5) break;
    }
  }

  std::cout << "Total found: " << found << "\n";
  return 0;
}
