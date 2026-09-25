#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

struct Box2D {
  double x1, x2, y1, y2;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // Lean ax0
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0_raw = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
                 ctr0.y.ToDouble() / ax0.B.ToDouble(),
                 ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0 = yocto::normalize(u0_raw);
  double norm_u0 = yocto::length(u0_raw);

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.015;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double R = std::tan(alpha);
  double c_core = 0.0003;

  std::cout << "norm(u0) = " << norm_u0 << ", cos(alpha) = " << cos_alpha << ", alpha = " << alpha * 180.0 / M_PI << " deg\n";
  std::cout << "Disk radius R in projective plane = " << R << "\n";

  std::vector<vec3> all_v;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    all_v.push_back(v);
  }

  // Check if box overlaps disk:
  auto box_overlaps_disk = [&](const Box2D& b) {
    double cx = std::max(b.x1, std::min(0.0, b.x2));
    double cy = std::max(b.y1, std::min(0.0, b.y2));
    return (cx * cx + cy * cy) <= R * R;
  };

  // Find covering axis for box:
  auto find_cover = [&](const Box2D& b) {
    vec3 p[4] = {
      u0 + b.x1 * ex + b.y1 * ey,
      u0 + b.x1 * ex + b.y2 * ey,
      u0 + b.x2 * ex + b.y1 * ey,
      u0 + b.x2 * ex + b.y2 * ey
    };
    double len_p[4] = {yocto::length(p[0]), yocto::length(p[1]), yocto::length(p[2]), yocto::length(p[3])};

    for (size_t i = 0; i < all_v.size(); i++) {
      bool ok = true;
      for (int k = 0; k < 4; k++) {
        if (yocto::dot(p[k], all_v[i]) < c_core * len_p[k]) {
          ok = false;
          break;
        }
      }
      if (ok) return (int)i;
    }
    return -1;
  };

  struct Node {
    Box2D b;
    int depth;
  };
  std::vector<Node> stack = {{{-R, R, -R, R}, 0}};
  int total_certified_leaves = 0;
  int total_outside = 0;
  int max_depth = 0;

  while (!stack.empty()) {
    Node node = stack.back();
    stack.pop_back();

    if (!box_overlaps_disk(node.b)) {
      total_outside++;
      continue;
    }

    int axis_idx = find_cover(node.b);
    if (axis_idx >= 0) {
      total_certified_leaves++;
      if (node.depth > max_depth) max_depth = node.depth;
      continue;
    }

    if (node.depth >= 10) {
      std::cout << "Failed at depth " << node.depth << ": ["
                << node.b.x1 << ", " << node.b.x2 << "] x [" << node.b.y1 << ", " << node.b.y2 << "]\n";
      break;
    }

    double mx = 0.5 * (node.b.x1 + node.b.x2);
    double my = 0.5 * (node.b.y1 + node.b.y2);
    stack.push_back({{node.b.x1, mx, node.b.y1, my}, node.depth + 1});
    stack.push_back({{mx, node.b.x2, node.b.y1, my}, node.depth + 1});
    stack.push_back({{node.b.x1, mx, my, node.b.y2}, node.depth + 1});
    stack.push_back({{mx, node.b.x2, my, node.b.y2}, node.depth + 1});
  }

  std::cout << "Result: total_certified_leaves = " << total_certified_leaves
            << ", total_outside = " << total_outside
            << ", max_depth = " << max_depth << "\n";

  return 0;
}
