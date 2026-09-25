#include <iostream>
#include <vector>
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

  vec3 u0 = {-0.01389, 0.01857, -0.06689};
  double c_cone = 0.038;
  double c = 0.00001;
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

  std::vector<size_t> pool_neg_y;
  std::vector<size_t> pool_pos_x;
  std::vector<size_t> pool_neg_x;
  std::vector<size_t> pool_pos_z;

  for (size_t i = 0; i < base_axes.size(); i++) {
    vec3 c = ToDouble(base_axes[i].center);
    if (c.y < -0.01) pool_neg_y.push_back(i);
    if (c.x > 0.03) pool_pos_x.push_back(i);
    if (c.x < -0.03) pool_neg_x.push_back(i);
    if (c.z > 0.02) pool_pos_z.push_back(i);
  }

  std::cout << "Pools: neg_y=" << pool_neg_y.size()
            << ", pos_x=" << pool_pos_x.size()
            << ", neg_x=" << pool_neg_x.size()
            << ", pos_z=" << pool_pos_z.size() << "\n";

  int found = 0;
  for (size_t i1 : pool_neg_y) {
    const vec3 &v1 = ToDouble(base_axes[i1].center);
    for (size_t i2 : pool_pos_x) {
      if (i2 == i1) continue;
      const vec3 &v2 = ToDouble(base_axes[i2].center);
      for (size_t i3 : pool_neg_x) {
        if (i3 == i1 || i3 == i2) continue;
        const vec3 &v3 = ToDouble(base_axes[i3].center);

        bool ok = true;
        for (int k = 0; k < 6; k++) {
          if (!InTetrahedron(v0, v1, v2, v3, targets[k], 1e-6)) {
            ok = false;
            break;
          }
        }
        if (ok) {
          std::cout << "FOUND WINNER! i1=" << i1 << " (neg_y), i2=" << i2 << " (pos_x), i3=" << i3 << " (neg_x)\n";
          found++;
          if (found >= 10) goto done;
        }
      }
    }
  }
done:
  std::cout << "Total found: " << found << "\n";
  return 0;
}
