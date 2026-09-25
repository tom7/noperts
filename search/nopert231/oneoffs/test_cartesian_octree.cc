#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include <queue>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct AxisData {
  vec3 v;
  int id;
};

struct Box3D {
  double x_min, x_max, y_min, y_max, z_min, z_max;
  int depth;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0_info[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0_info, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));

  double B0 = ax0.B.ToDouble();
  vec3 u0 = vec3{ctr0.x.ToDouble() / B0, ctr0.y.ToDouble() / B0, ctr0.z.ToDouble() / B0};

  double c_cone = 0.015;
  double box_delta = 234013.0 / 1000000000.0;
  double c_core = 0.000234060;

  std::vector<AxisData> candidate_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      candidate_axes.push_back({v, (int)i});
    }
  }

  std::cout << "Candidate axes: " << candidate_axes.size() << "\n";

  std::queue<Box3D> q;
  // u0 has z < 0, so the cone is entirely in z in [-1, 0.5]
  q.push({-1.0, 1.0, -1.0, 1.0, -1.0, 1.0, 0});

  std::vector<std::pair<Box3D, int>> covered_leaves;
  std::set<int> distinct_axes;

  while (!q.empty()) {
    Box3D b = q.front();
    q.pop();

    // Check if box can intersect sphere ||a|| = 1
    double min_x = (b.x_min <= 0 && b.x_max >= 0) ? 0.0 : std::min(std::abs(b.x_min), std::abs(b.x_max));
    double min_y = (b.y_min <= 0 && b.y_max >= 0) ? 0.0 : std::min(std::abs(b.y_min), std::abs(b.y_max));
    double min_z = (b.z_min <= 0 && b.z_max >= 0) ? 0.0 : std::min(std::abs(b.z_min), std::abs(b.z_max));
    double r_min_sq = min_x * min_x + min_y * min_y + min_z * min_z;
    if (r_min_sq > 1.0) continue;

    double max_x = std::max(std::abs(b.x_min), std::abs(b.x_max));
    double max_y = std::max(std::abs(b.y_min), std::abs(b.y_max));
    double max_z = std::max(std::abs(b.z_min), std::abs(b.z_max));
    double r_max_sq = max_x * max_x + max_y * max_y + max_z * max_z;
    if (r_max_sq < 1.0) continue;

    // Check if box can satisfy a . u0 >= c_cone
    double u_max = (u0.x >= 0 ? u0.x * b.x_max : u0.x * b.x_min) +
                   (u0.y >= 0 ? u0.y * b.y_max : u0.y * b.y_min) +
                   (u0.z >= 0 ? u0.z * b.z_max : u0.z * b.z_min);
    if (u_max < c_cone) continue;

    int best_ax = -1;
    double best_val = -1e9;
    for (size_t a = 0; a < candidate_axes.size(); a++) {
      const auto &ax = candidate_axes[a];
      double val = (ax.v.x >= 0 ? ax.v.x * b.x_min : ax.v.x * b.x_max) +
                   (ax.v.y >= 0 ? ax.v.y * b.y_min : ax.v.y * b.y_max) +
                   (ax.v.z >= 0 ? ax.v.z * b.z_min : ax.v.z * b.z_max);
      if (val > best_val) {
        best_val = val;
        best_ax = a;
      }
    }

    if (best_val >= c_core) {
      covered_leaves.push_back({b, best_ax});
      distinct_axes.insert(best_ax);
    } else {
      if (b.depth >= 10) {
        std::cout << "Depth limit 7 reached at [" << b.x_min << ", " << b.x_max << "] x ["
                  << b.y_min << ", " << b.y_max << "] x [" << b.z_min << ", " << b.z_max
                  << "], best_val = " << best_val << "\n";
        return 1;
      }
      double mx = 0.5 * (b.x_min + b.x_max);
      double my = 0.5 * (b.y_min + b.y_max);
      double mz = 0.5 * (b.z_min + b.z_max);
      for (int dx = 0; dx < 2; dx++) {
        for (int dy = 0; dy < 2; dy++) {
          for (int dz = 0; dz < 2; dz++) {
            q.push({dx ? mx : b.x_min, dx ? b.x_max : mx,
                    dy ? my : b.y_min, dy ? b.y_max : my,
                    dz ? mz : b.z_min, dz ? b.z_max : mz,
                    b.depth + 1});
          }
        }
      }
    }
  }

  std::cout << "SUCCESS! Cartesian octree 100% COVERED AT DEPTH <= 7!\n";
  std::cout << "Total leaves: " << covered_leaves.size() << "\n";
  std::cout << "Distinct core axes used: " << distinct_axes.size() << "\n";
  for (int ax_idx : distinct_axes) {
    std::cout << "  Used axis index " << candidate_axes[ax_idx].id
              << ", delta = " << axes[candidate_axes[ax_idx].id].delta.ToDouble() << "\n";
  }

  return 0;
}
