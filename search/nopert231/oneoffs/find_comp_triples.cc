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
  double norm_sq() const { return dot(*this); }
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

  // Load ax0:
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate cert0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &cert0, &ctr0, &del0, &err, BigRat(1, 1000));
  Vec3 u0 = {ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()};

  struct Cand {
    int idx;
    Vec3 u;
    Tube229::AuditedAxis ax;
  };
  std::vector<Cand> all_cands;

  double box_delta = 234013.0 / 1000000000.0;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      Vec3 u = {ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()};
      all_cands.push_back({(int)i, u, ax});
    }
  }

  // Filter top candidates by extreme directions
  std::vector<Cand> pool_x = all_cands;
  std::sort(pool_x.begin(), pool_x.end(), [](const Cand &a, const Cand &b) { return a.u.x > b.u.x; });
  std::vector<Cand> pool_my = all_cands;
  std::sort(pool_my.begin(), pool_my.end(), [](const Cand &a, const Cand &b) { return a.u.y < b.u.y; });
  std::vector<Cand> pool_z = all_cands;
  std::sort(pool_z.begin(), pool_z.end(), [](const Cand &a, const Cand &b) { return a.u.z > b.u.z; });

  std::set<int> seen;
  std::vector<Cand> cands;
  auto add_pool = [&](const std::vector<Cand> &p, int n) {
    for (int i = 0; i < n && i < (int)p.size(); i++) {
      if (seen.insert(p[i].idx).second) cands.push_back(p[i]);
    }
  };
  add_pool(pool_x, 30);
  add_pool(pool_my, 30);
  add_pool(pool_z, 30);

  std::cout << "Testing pool of " << cands.size() << " candidates.\n";

  double c = 0.001;
  double delta = box_delta;
  double c_cone = 0.055; // Let's test 0.055 directly!
  double scale0 = (c + delta) / c_cone;
  Vec3 v0 = {scale0 * u0.x, scale0 * u0.y, scale0 * u0.z};

  double oct_r = 1.75 * (c + delta);
  Vec3 targets[6] = {
    {oct_r, 0, 0}, {-oct_r, 0, 0},
    {0, oct_r, 0}, {0, -oct_r, 0},
    {0, 0, oct_r}, {0, 0, -oct_r}
  };

  int found = 0;
  for (size_t i1 = 0; i1 < cands.size() && found < 5; i1++) {
    const Vec3 &u1 = cands[i1].u;
    for (size_t i2 = i1 + 1; i2 < cands.size() && found < 5; i2++) {
      const Vec3 &u2 = cands[i2].u;
      for (size_t i3 = i2 + 1; i3 < cands.size() && found < 5; i3++) {
        const Vec3 &u3 = cands[i3].u;

        Vec3 col0 = {v0.x - u3.x, v0.y - u3.y, v0.z - u3.z};
        Vec3 col1 = {u1.x - u3.x, u1.y - u3.y, u1.z - u3.z};
        Vec3 col2 = {u2.x - u3.x, u2.y - u3.y, u2.z - u3.z};

        bool all_pos = true;
        double min_b = 1.0;
        for (int k = 0; k < 6; k++) {
          Vec3 rhs = {targets[k].x - u3.x, targets[k].y - u3.y, targets[k].z - u3.z};
          double b012[3];
          if (!solve3(col0, col1, col2, rhs, b012)) {
            all_pos = false; break;
          }
          double b3 = 1.0 - b012[0] - b012[1] - b012[2];
          double mb = std::min({b012[0], b012[1], b012[2], b3});
          if (mb < 0) {
            all_pos = false; break;
          }
          if (mb < min_b) min_b = mb;
        }

        if (all_pos && min_b > 1e-4) {
          found++;
          std::cout << "WINNER #" << found << ": axes ("
                    << cands[i1].idx << ", " << cands[i2].idx << ", " << cands[i3].idx
                    << "), min_b = " << min_b << "\n";
          std::cout << "  cands[i1].ax cert B=" << cands[i1].ax.cert.B.ToDouble() << "\n";
          std::cout << "  cands[i2].ax cert B=" << cands[i2].ax.cert.B.ToDouble() << "\n";
          std::cout << "  cands[i3].ax cert B=" << cands[i3].ax.cert.B.ToDouble() << "\n";
        }
      }
    }
  }

  if (found == 0) {
    std::cout << "No triple found.\n";
  }

  return 0;
}
