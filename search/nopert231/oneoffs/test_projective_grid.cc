#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

struct Rect {
  double x0, x1, y0, y1;
};

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});

  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double c_cone = 0.015;
  double norm_u0 = yocto::length(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  double cos_alpha = c_cone / norm_u0;
  double sin_alpha = std::sqrt(1.0 - cos_alpha * cos_alpha);
  double R = sin_alpha / cos_alpha;
  std::cout << "Cone half-angle alpha: " << std::acos(cos_alpha) * 180.0 / M_PI << " deg\n";
  std::cout << "cos_alpha = " << cos_alpha << ", projective radius R = " << R << "\n";

  // In the orthonormal basis (e1, e2, u0):
  // Any ray is (x e1 + y e2 + u0) / sqrt(1 + x^2 + y^2).
  // For any axis v:
  // dot(ray, v) = (x dot(e1, v) + y dot(e2, v) + dot(u0, v)) / sqrt(1 + x^2 + y^2).
  // In the disk x^2 + y^2 <= R^2, sqrt(1 + x^2 + y^2) <= sqrt(1 + R^2) = 1 / cos_alpha.
  // So dot(ray, v) >= cos_alpha * (x A + y B + C), where:
  // A = dot(e1, v), B = dot(e2, v), C = dot(u0, v).

  // All 5000 axes in basis (e1, e2, u0):
  struct AxisLinear {
    double A, B, C;
  };
  std::vector<AxisLinear> lin_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = yocto::normalize(vec3{axes[i].center.x.ToDouble(), axes[i].center.y.ToDouble(), axes[i].center.z.ToDouble()});
    lin_axes.push_back({yocto::dot(e1, v), yocto::dot(e2, v), yocto::dot(u0, v)});
  }

  double c_core = 0.002;

  // Let's test a quadtree covering the bounding square [-R, R] x [-R, R]:
  std::vector<Rect> queue;
  queue.push_back({-R, R, -R, R});

  int max_depth = 13;
  int leaves_checked = 0;
  int leaves_failed = 0;

  auto overlaps_disk = [&](const Rect &r) {
    // Check if rectangle intersects disk x^2 + y^2 <= R^2
    double cx = std::max(r.x0, std::min(0.0, r.x1));
    double cy = std::max(r.y0, std::min(0.0, r.y1));
    return (cx * cx + cy * cy) <= R * R;
  };

  std::vector<Rect> work = queue;
  for (int depth = 0; depth < max_depth; depth++) {
    std::vector<Rect> next_work;
    for (const auto &r : work) {
      if (!overlaps_disk(r)) continue;

      // Check if ANY axis covers all 4 corners with margin >= c_core:
      // Note: at any point (x, y), dot = (x A + y B + C) / sqrt(1 + x^2 + y^2).
      // Since (x A + y B + C) is affine, if it is positive and at all 4 corners:
      // min_{(x,y) in r} dot(x, y) >= min_corners (x A + y B + C) / max_corners sqrt(1 + x^2 + y^2).
      double max_r_sq = std::max({r.x0*r.x0 + r.y0*r.y0, r.x0*r.x0 + r.y1*r.y1,
                                  r.x1*r.x0 + r.y0*r.y0, r.x1*r.x1 + r.y1*r.y1});
      double denom = std::sqrt(1.0 + max_r_sq);

      bool covered = false;
      for (size_t i = 0; i < lin_axes.size(); i++) {
        const auto &ax = lin_axes[i];
        double num00 = ax.A * r.x0 + ax.B * r.y0 + ax.C;
        double num01 = ax.A * r.x0 + ax.B * r.y1 + ax.C;
        double num10 = ax.A * r.x1 + ax.B * r.y0 + ax.C;
        double num11 = ax.A * r.x1 + ax.B * r.y1 + ax.C;
        double min_num = std::min({num00, num01, num10, num11});
        if (min_num / denom >= c_core) {
          covered = true;
          break;
        }
      }

      if (covered) {
        leaves_checked++;
      } else {
        // Subdivide
        double mx = 0.5 * (r.x0 + r.x1);
        double my = 0.5 * (r.y0 + r.y1);
        next_work.push_back({r.x0, mx, r.y0, my});
        next_work.push_back({mx, r.x1, r.y0, my});
        next_work.push_back({r.x0, mx, my, r.y1});
        next_work.push_back({mx, r.x1, my, r.y1});
      }
    }
    work = std::move(next_work);
    std::cout << "Depth " << depth << ": " << leaves_checked << " cells closed, "
              << work.size() << " cells pending.\n";
    if (work.empty()) break;
  }

  std::cout << "Done! Total closed cells: " << leaves_checked << ", remaining: " << work.size() << "\n";

  return 0;
}
