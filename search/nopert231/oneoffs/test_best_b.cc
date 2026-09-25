#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <set>
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

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate cert0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &cert0, &ctr0, &del0, &err, BigRat(1, 1000));
  Vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};

  struct Cand { int idx; Vec3 u; };
  std::vector<Cand> all_cands;

  double box_delta = 234013.0 / 1000000000.0;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      Vec3 u = {ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()};
      all_cands.push_back({(int)i, u});
    }
  }

  double c = 0.001;
  double delta = box_delta;
  double c_cone = 0.055;
  double scale0 = (c + delta) / c_cone;
  Vec3 v0 = {scale0 * u0.x, scale0 * u0.y, scale0 * u0.z};

  double oct_r = 1.75 * (c + delta);
  Vec3 targets[6] = {
    {oct_r, 0, 0}, {-oct_r, 0, 0},
    {0, oct_r, 0}, {0, -oct_r, 0},
    {0, 0, oct_r}, {0, 0, -oct_r}
  };

  // Test random triples or sample triples to see min_b distribution
  double best_min_b = -1e9;
  int best_i1=-1, best_i2=-1, best_i3=-1;

  // Let's test a uniform stride sample of all_cands
  std::vector<Cand> sample;
  for (size_t i = 0; i < all_cands.size(); i += 40) sample.push_back(all_cands[i]);
  std::cout << "Testing sample of " << sample.size() << " candidates...\n";

  for (size_t i1 = 0; i1 < sample.size(); i1++) {
    for (size_t i2 = i1 + 1; i2 < sample.size(); i2++) {
      for (size_t i3 = i2 + 1; i3 < sample.size(); i3++) {
        Vec3 u1 = sample[i1].u, u2 = sample[i2].u, u3 = sample[i3].u;
        Vec3 col0 = {v0.x - u3.x, v0.y - u3.y, v0.z - u3.z};
        Vec3 col1 = {u1.x - u3.x, u1.y - u3.y, u1.z - u3.z};
        Vec3 col2 = {u2.x - u3.x, u2.y - u3.y, u2.z - u3.z};
        double worst_b = 1.0;
        for (int k = 0; k < 6; k++) {
          Vec3 rhs = {targets[k].x - u3.x, targets[k].y - u3.y, targets[k].z - u3.z};
          double b012[3];
          if (!solve3(col0, col1, col2, rhs, b012)) { worst_b = -1e9; break; }
          double b3 = 1.0 - b012[0] - b012[1] - b012[2];
          double mb = std::min({b012[0], b012[1], b012[2], b3});
          if (mb < worst_b) worst_b = mb;
        }
        if (worst_b > best_min_b) {
          best_min_b = worst_b;
          best_i1 = sample[i1].idx; best_i2 = sample[i2].idx; best_i3 = sample[i3].idx;
        }
      }
    }
  }
  std::cout << "Best min_b found = " << best_min_b << " for axes ("
            << best_i1 << ", " << best_i2 << ", " << best_i3 << ")\n";
  return 0;
}
