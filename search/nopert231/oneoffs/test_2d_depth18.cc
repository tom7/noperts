#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include <queue>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Axis2D {
  double vx, vy, vz;
  int id;
};

struct Box2D {
  double x_min, x_max, y_min, y_max;
  int depth;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

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
  double norm_u0 = std::sqrt(yocto::dot(u0, u0));
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double c_cone = 0.017;
  double box_delta = 200.0 / 1000000.0;
  double c_core = 200.0 / 1000000.0;

  double cos_min = c_cone / norm_u0;
  double max_R = std::sqrt(1.0 / (cos_min * cos_min) - 1.0);
  std::cout << "Cone half-angle: " << (std::acos(cos_min) * 180.0 / M_PI) << " deg, max_R = " << max_R << "\n";

  std::vector<Axis2D> candidate_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      candidate_axes.push_back({yocto::dot(v, k1), yocto::dot(v, k2), yocto::dot(v, e3), (int)i});
    }
  }

  std::cout << "Total candidate core axes: " << candidate_axes.size() << "\n";

  std::queue<Box2D> q;
  q.push({-max_R, max_R, -max_R, max_R, 0});

  std::vector<std::pair<Box2D, int>> covered_leaves;
  std::set<int> distinct_axes;
  int failed_leaves = 0;

  while (!q.empty()) {
    Box2D b = q.front();
    q.pop();

    double min_x = (b.x_min <= 0 && b.x_max >= 0) ? 0.0 : std::min(std::abs(b.x_min), std::abs(b.x_max));
    double min_y = (b.y_min <= 0 && b.y_max >= 0) ? 0.0 : std::min(std::abs(b.y_min), std::abs(b.y_max));
    if (min_x * min_x + min_y * min_y > max_R * max_R) continue;

    double max_x = std::max(std::abs(b.x_min), std::abs(b.x_max));
    double max_y = std::max(std::abs(b.y_min), std::abs(b.y_max));
    double max_norm = std::sqrt(1.0 + max_x * max_x + max_y * max_y);

    int best_ax = -1;
    double best_margin = -1e9;

    for (size_t a = 0; a < candidate_axes.size(); a++) {
      const auto &ax = candidate_axes[a];
      double min_linear = (ax.vx >= 0 ? ax.vx * b.x_min : ax.vx * b.x_max) +
                          (ax.vy >= 0 ? ax.vy * b.y_min : ax.vy * b.y_max) +
                          ax.vz;
      double margin = min_linear - c_core * max_norm;
      if (margin > best_margin) {
        best_margin = margin;
        best_ax = a;
        if (margin >= 0) break;
      }
    }

    if (best_margin >= 0) {
      covered_leaves.push_back({b, best_ax});
      distinct_axes.insert(candidate_axes[best_ax].id);
    } else {
      if (b.depth >= 18) {
        failed_leaves++;
        if (failed_leaves <= 5) {
          std::cout << "Depth limit 18 reached at [" << b.x_min << ", " << b.x_max << "] x ["
                    << b.y_min << ", " << b.y_max << "], best_margin = " << best_margin << "\n";
        }
        continue;
      }
      double mx = 0.5 * (b.x_min + b.x_max);
      double my = 0.5 * (b.y_min + b.y_max);
      q.push({b.x_min, mx, b.y_min, my, b.depth + 1});
      q.push({mx, b.x_max, b.y_min, my, b.depth + 1});
      q.push({b.x_min, mx, my, b.y_max, b.depth + 1});
      q.push({mx, b.x_max, my, b.y_max, b.depth + 1});
    }
  }

  if (failed_leaves > 0) {
    std::cout << "FAILED: " << failed_leaves << " leaves could not be covered at depth 18.\n";
  } else {
    std::cout << "SUCCESS! 100% OF ADVERSARY CONE COVERED IN 2D!\n";
    std::cout << "Total covered leaves: " << covered_leaves.size() << "\n";
    std::cout << "Distinct core axes used: " << distinct_axes.size() << "\n";
  }
  return 0;
}
