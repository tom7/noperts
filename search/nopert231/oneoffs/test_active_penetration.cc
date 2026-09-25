#include <iostream>
#include <vector>
#include <iomanip>
#include <cmath>

#include "ruperts/tubetree229.h"
#include "ruperts/nopert229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;
using vec2 = Tube229::vec2;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 u = yocto::normalize(vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()});

  vec3 axis = vec3{0, 1, 0};
  vec3 first = yocto::normalize(yocto::cross(u, axis));
  vec3 second = yocto::cross(u, first);

  std::vector<vec2> outer_pts(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    outer_pts[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> hull = Tube229::ConvexHull2D(outer_pts);
  int H = hull.size();

  vec3 omega = yocto::normalize(vec3{-0.400992, 0.483041, 0.778381});
  vec3 w = -omega;

  std::vector<vec2> normals(H);
  std::vector<double> offsets(H);
  for (int i = 0; i < H; i++) {
    int v0 = hull[i];
    int v1 = hull[(i + 1) % H];
    vec2 edge = outer_pts[v1] - outer_pts[v0];
    vec2 n = vec2{edge.y, -edge.x}; // outward normal
    n = n / yocto::length(vec3{n.x, n.y, 0});
    normals[i] = n;
    offsets[i] = normals[i].x * outer_pts[v0].x + normals[i].y * outer_pts[v0].y;
  }

  double theta = 1e-5;
  std::vector<vec2> inner_pts(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    vec3 v = Vertex(k);
    vec3 v_rot = v + std::sin(theta) * yocto::cross(w, v) + (1.0 - std::cos(theta)) * yocto::cross(w, yocto::cross(w, v));
    inner_pts[k] = vec2{yocto::dot(v_rot, first), yocto::dot(v_rot, second)};
  }

  // Linear program to find exact minimax:
  // min gamma
  // s.t. normals[i] . (inner_pts[k] + t) - offsets[i] <= gamma  forall k, i
  // Let's sample fine grid around optimal
  double best_max_pen = 1e9;
  vec2 best_t = {0, 0};
  for (double tx = 1.5e-6; tx <= 1.7e-6; tx += 1e-9) {
    for (double ty = -1.5e-6; ty <= -1.3e-6; ty += 1e-9) {
      vec2 t = {tx, ty};
      double max_pen = -1e9;
      for (int k = 0; k < NUM_VERTICES; k++) {
        vec2 p = inner_pts[k] + t;
        for (int i = 0; i < H; i++) {
          double pen = normals[i].x * p.x + normals[i].y * p.y - offsets[i];
          if (pen > max_pen) max_pen = pen;
        }
      }
      if (max_pen < best_max_pen) {
        best_max_pen = max_pen;
        best_t = t;
      }
    }
  }

  std::cout << "Optimal t: (" << best_t.x << ", " << best_t.y << ")\n";
  std::cout << "Minimax penetration: " << best_max_pen << " (rate: " << best_max_pen / theta << ")\n";
  std::cout << "Active constraints within 1e-8 of max:\n";
  for (int k = 0; k < NUM_VERTICES; k++) {
    vec2 p = inner_pts[k] + best_t;
    for (int i = 0; i < H; i++) {
      double pen = normals[i].x * p.x + normals[i].y * p.y - offsets[i];
      if (pen >= best_max_pen - 1e-8) {
        std::cout << "  Inner vertex " << k << " penetrating Edge "
                  << hull[i] << "->" << hull[(i+1)%H]
                  << " (normal: " << normals[i].x << ", " << normals[i].y << ")"
                  << " pen = " << pen << "\n";
      }
    }
  }

  return 0;
}
// Just test v10 and v15 penetration at best_t
