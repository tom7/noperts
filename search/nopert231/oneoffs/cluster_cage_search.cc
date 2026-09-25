#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  vec3 tri_f[3] = { ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2]) };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});

  // Collect pool with delta <= 0.000200
  std::vector<std::pair<int, vec3>> full_pool;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000200) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      full_pool.push_back({(int)i, v});
    }
  }

  // Greedy diversity clustering to ~200 points
  std::vector<std::pair<int, vec3>> pool;
  double min_dist_thresh = 0.025;
  for (const auto &item : full_pool) {
    bool keep = true;
    for (const auto &p : pool) {
      if (yocto::length(item.second - p.second) < min_dist_thresh) {
        keep = false;
        break;
      }
    }
    if (keep) pool.push_back(item);
  }
  std::cout << "Full pool: " << full_pool.size() << ", clustered pool: " << pool.size() << "\n";

  double c_cone = 0.017;
  double c_box = 0.001;
  double delta = 0.000196;
  double R = 1.75 * (c_box + delta);
  vec3 targets[6] = {
    {+R, 0, 0}, {-R, 0, 0},
    {0, +R, 0}, {0, -R, 0},
    {0, 0, +R}, {0, 0, -R}
  };

  int zero_cands[] = {36, 37, 43, 44, 45, 46, 47, 49, 50, 51, 52};
  int P = pool.size();

  for (int ci : zero_cands) {
    ContactInfo c0[3] = { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, contacts[ci] };
    AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
    if (!Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0))) continue;

    vec3 u0 = vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
    vec3 v0 = ((c_box + delta) / c_cone) * u0;

    double best_min_b = -1e9;
    int bi = -1, bj = -1, bk = -1;

    for (int i = 0; i < P; i++) {
      vec3 v1 = pool[i].second;
      for (int j = i + 1; j < P; j++) {
        vec3 v2 = pool[j].second;
        for (int k = j + 1; k < P; k++) {
          vec3 v3 = pool[k].second;

          vec3 d0 = v0 - v3;
          vec3 d1 = v1 - v3;
          vec3 d2 = v2 - v3;
          double det = Det3(d0, d1, d2);
          if (std::abs(det) < 1e-7) continue;

          double min_b = 1e9;
          for (int t = 0; t < 6; t++) {
            vec3 dp = targets[t] - v3;
            double b0 = Det3(dp, d1, d2) / det;
            double b1 = Det3(d0, dp, d2) / det;
            double b2 = Det3(d0, d1, dp) / det;
            double b3 = 1.0 - b0 - b1 - b2;
            min_b = std::min({min_b, b0, b1, b2, b3});
          }
          if (min_b > best_min_b) {
            best_min_b = min_b;
            bi = pool[i].first; bj = pool[j].first; bk = pool[k].first;
            if (min_b > 1e-4) {
              std::cout << "FOUND WINNER for cand " << ci << "! min_b = " << min_b
                        << ", axes = (" << bi << ", " << bj << ", " << bk << ")\n";
              goto next_cand;
            }
          }
        }
      }
    }
    std::cout << "Cand " << ci << ": best min_b = " << best_min_b << "\n";
  next_cand:;
  }

  return 0;
}
