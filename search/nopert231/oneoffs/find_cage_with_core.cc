#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Vec3 {
  double x, y, z;
  double dot(const Vec3 &o) const { return x*o.x + y*o.y + z*o.z; }
  static Vec3 cross(const Vec3 &a, const Vec3 &b) {
    return {a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x};
  }
};

bool solve3(const Vec3 &c0, const Vec3 &c1, const Vec3 &c2, const Vec3 &rhs, double b[3]) {
  double d = c0.dot(Vec3::cross(c1, c2));
  if (std::abs(d) < 1e-12) return false;
  b[0] = rhs.dot(Vec3::cross(c1, c2)) / d;
  b[1] = c0.dot(Vec3::cross(rhs, c2)) / d;
  b[2] = c0.dot(Vec3::cross(c1, rhs)) / d;
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  double box_delta = 234013.0 / 1000000000.0;
  double c = 0.001;
  double delta = box_delta;
  double oct_r = 1.75 * (c + delta);
  Vec3 targets[6] = {
    {oct_r, 0, 0}, {-oct_r, 0, 0},
    {0, oct_r, 0}, {0, -oct_r, 0},
    {0, 0, oct_r}, {0, 0, -oct_r}
  };

  // Axis 2951 is our core axis
  int core_idx = 2951;
  const auto &core_ax = axes[core_idx];
  Vec3 u0 = {core_ax.center.x.ToDouble(), core_ax.center.y.ToDouble(), core_ax.center.z.ToDouble()};
  std::cout << "Core axis 2951 center: (" << u0.x << ", " << u0.y << ", " << u0.z << ")\n";
  std::cout << "Core axis 2951 delta: " << core_ax.delta.ToDouble() << " (box delta: " << box_delta << ")\n";

  // Collect candidate axes with delta <= box_delta
  struct Cand { int idx; Vec3 u; };
  std::vector<Cand> cands;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= box_delta) {
      Vec3 u = {axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()};
      cands.push_back({(int)i, u});
    }
  }
  std::cout << "Total candidates with delta <= box_delta: " << cands.size() << "\n";

  // Let's test if any triple (u1, u2, u3) along with u0 forms a valid cage!
  // Note: if u0 is the exceptional axis with theta = 0, scale0 = (c + delta)/c_cone.
  // With c_cone = c + delta, scale0 = 1.0! That is, NO contraction needed!
  // Or with c_cone = 2 * (c + delta), scale0 = 0.5.
  // Let's first test scale0 = 1.0 (c_cone = c + delta):
  double scale0 = 1.0;
  Vec3 v0 = {scale0 * u0.x, scale0 * u0.y, scale0 * u0.z};

  int found = 0;
  for (size_t i1 = 0; i1 < cands.size() && found < 5; i1++) {
    for (size_t i2 = i1 + 1; i2 < cands.size() && found < 5; i2++) {
      for (size_t i3 = i2 + 1; i3 < cands.size() && found < 5; i3++) {
        Vec3 u1 = cands[i1].u, u2 = cands[i2].u, u3 = cands[i3].u;
        Vec3 col0 = {v0.x - u3.x, v0.y - u3.y, v0.z - u3.z};
        Vec3 col1 = {u1.x - u3.x, u1.y - u3.y, u1.z - u3.z};
        Vec3 col2 = {u2.x - u3.x, u2.y - u3.y, u2.z - u3.z};
        bool ok = true;
        for (int k = 0; k < 6; k++) {
          Vec3 rhs = {targets[k].x - u3.x, targets[k].y - u3.y, targets[k].z - u3.z};
          double b012[3];
          if (!solve3(col0, col1, col2, rhs, b012)) { ok = false; break; }
          double b3 = 1.0 - b012[0] - b012[1] - b012[2];
          if (b012[0] < 0 || b012[1] < 0 || b012[2] < 0 || b3 < 0) { ok = false; break; }
        }
        if (ok) {
          std::cout << "FOUND CAGE WITH AXIS 2951: (" << cands[i1].idx << ", "
                    << cands[i2].idx << ", " << cands[i3].idx << ")\n";
          found++;
        }
      }
    }
  }
  if (found == 0) {
    std::cout << "No cage found with axis 2951 directly at scale 1.0. Let's test other axes!\n";
  }
  return 0;
}
