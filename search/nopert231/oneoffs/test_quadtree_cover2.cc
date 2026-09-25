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
  double c0, c1, c2;
  int id;
  AxisCertificate cert;
};

struct Box2D {
  double x_min, x_max, y_min, y_max;
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
  double norm_u0 = yocto::length(u0);
  vec3 e3 = u0 / norm_u0;

  vec3 temp = {1.0, 0.0, 0.0};
  if (std::abs(yocto::dot(temp, e3)) > 0.9) temp = {0.0, 1.0, 0.0};
  vec3 k1 = yocto::normalize(temp - yocto::dot(temp, e3) * e3);
  vec3 k2 = yocto::normalize(yocto::cross(e3, k1));

  double c_cone = 0.015;
  double c_core = 0.000234060;
  double box_delta = 234013.0 / 1000000000.0;
  double cos_max = c_cone / norm_u0;
  double R = std::sqrt(std::max(0.0, 1.0 - cos_max * cos_max));

  std::vector<AxisData> candidate_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax = axes[i];
    if (ax.delta.ToDouble() <= box_delta) {
      double B = ax.cert.B.ToDouble();
      vec3 v = vec3{ax.center.x.ToDouble() / B, ax.center.y.ToDouble() / B, ax.center.z.ToDouble() / B};
      double c1 = yocto::dot(v, k1);
      double c2 = yocto::dot(v, k2);
      double c0 = yocto::dot(v, u0) / (norm_u0 * norm_u0);
      if (c0 >= 0) {
        candidate_axes.push_back({v, c0, c1, c2, (int)i, ax.cert});
      }
    }
  }

  // Also add audited axes with small delta
  for (int m1 = 0; m1 <= 1000; m1 += 25) {
    for (int m2 = 0; m2 <= 1000; m2 += 25) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate ax_cert;
      BigVecQ3 center;
      BigRat delta;
      if (Tube229::AuditAxis(tri, contacts, &ax_cert, &center, &delta, &err, BigRat(0))) {
        if (delta.ToDouble() <= box_delta) {
          double B = ax_cert.B.ToDouble();
          vec3 v = vec3{center.x.ToDouble() / B, center.y.ToDouble() / B, center.z.ToDouble() / B};
          double c1 = yocto::dot(v, k1);
          double c2 = yocto::dot(v, k2);
          double c0 = yocto::dot(v, u0) / (norm_u0 * norm_u0);
          if (c0 >= 0) {
            candidate_axes.push_back({v, c0, c1, c2, -1, ax_cert});
          }
        }
      }
    }
  }

  std::cout << "Candidate axes: " << candidate_axes.size() << "\n";

  std::queue<Box2D> q;
  q.push({-R, R, -R, R, 0});

  std::vector<std::pair<Box2D, int>> covered_leaves;
  std::set<int> distinct_axes;

  while (!q.empty()) {
    Box2D b = q.front();
    q.pop();

    double cx = std::max(0.0, std::max(b.x_min, -b.x_max));
    double cy = std::max(0.0, std::max(b.y_min, -b.y_max));
    if (cx * cx + cy * cy > R * R) {
      continue;
    }

    int best_ax = -1;
    double best_val = -1e9;
    for (size_t a = 0; a < candidate_axes.size(); a++) {
      const auto &ax = candidate_axes[a];
      double c1_c = (ax.c1 >= 0) ? (ax.c1 * b.x_min) : (ax.c1 * b.x_max);
      double c2_c = (ax.c2 >= 0) ? (ax.c2 * b.y_min) : (ax.c2 * b.y_max);
      double val = c1_c + c2_c + ax.c0 * c_cone;
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
        std::cout << "Depth limit 10 reached at [" << b.x_min << ", " << b.x_max << "] x ["
                  << b.y_min << ", " << b.y_max << "], best_val = " << best_val << "\n";
        return 1;
      }
      double mx = 0.5 * (b.x_min + b.x_max);
      double my = 0.5 * (b.y_min + b.y_max);
      q.push({b.x_min, mx, b.y_min, my, b.depth + 1});
      q.push({mx, b.x_max, b.y_min, my, b.depth + 1});
      q.push({b.x_min, mx, my, b.y_max, b.depth + 1});
      q.push({mx, b.x_max, my, b.y_max, b.depth + 1});
    }
  }

  std::cout << "SUCCESS! Quadtree covered the entire cone!\n";
  std::cout << "Total leaves: " << covered_leaves.size() << "\n";
  std::cout << "Distinct core axes used: " << distinct_axes.size() << "\n";

  return 0;
}
