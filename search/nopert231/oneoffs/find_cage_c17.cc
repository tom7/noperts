#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <set>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  double delta = 0.000234013;
  double box_c = 0.001;

  std::vector<vec3> u_filtered;
  std::vector<int> orig_indices;
  for (size_t i = 0; i < base_axes.size(); i++) {
    if (base_axes[i].delta.ToDouble() <= delta) {
      u_filtered.push_back({base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
                            base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
                            base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()});
      orig_indices.push_back(i);
    }
  }

  std::vector<vec3> directions;
  for (int dx = -2; dx <= 2; dx++) {
    for (int dy = -2; dy <= 2; dy++) {
      for (int dz = -2; dz <= 2; dz++) {
        if (dx == 0 && dy == 0 && dz == 0) continue;
        directions.push_back(yocto::normalize(vec3{(double)dx, (double)dy, (double)dz}));
      }
    }
  }

  std::set<int> selected_indices;
  for (const auto &d : directions) {
    std::vector<std::pair<double, int>> ranked;
    for (size_t i = 0; i < u_filtered.size(); i++) {
      ranked.push_back({yocto::dot(u_filtered[i], d), (int)i});
    }
    std::sort(ranked.rbegin(), ranked.rend());
    for (int k = 0; k < std::min(15, (int)ranked.size()); k++) {
      selected_indices.insert(ranked[k].second);
    }
  }

  std::vector<int> pool(selected_indices.begin(), selected_indices.end());

  for (int c_cone_int = 15; c_cone_int <= 19; c_cone_int++) {
    double c_cone = c_cone_int / 1000.0;
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);
    std::vector<vec3> oct = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };

    int N = pool.size();
    double best_min_l = -1e9;
    int best_i = -1, best_j = -1, best_k = -1;

    for (int i = 0; i < N; i++) {
      vec3 v1 = u_filtered[pool[i]];
      for (int j = i + 1; j < N; j++) {
        vec3 v2 = u_filtered[pool[j]];
        for (int k = j + 1; k < N; k++) {
          vec3 v3 = u_filtered[pool[k]];

          vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
          double det = yocto::dot(d1, yocto::cross(d2, d3));
          if (std::abs(det) < 1e-8) continue;
          vec3 c23 = yocto::cross(d2, d3);

          double min_l = 1e9;
          for (const auto &p : oct) {
            vec3 dp = p - v0;
            double l1 = yocto::dot(dp, c23) / det;
            double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
            double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
            double l0 = 1.0 - l1 - l2 - l3;
            min_l = std::min({min_l, l0, l1, l2, l3});
            if (min_l <= best_min_l) break;
          }

          if (min_l > best_min_l) {
            best_min_l = min_l;
            best_i = orig_indices[pool[i]];
            best_j = orig_indices[pool[j]];
            best_k = orig_indices[pool[k]];
            if (best_min_l > 0) goto found_for_c;
          }
        }
      }
    }
  found_for_c:
    std::cout << "c_cone = " << c_cone << ": best_min_l = " << best_min_l
              << " with (" << best_i << ", " << best_j << ", " << best_k << ")\n";
  }

  return 0;
}
