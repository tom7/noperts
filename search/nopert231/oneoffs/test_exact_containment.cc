#include <iostream>
#include <vector>
#include <iomanip>
#include <cmath>

#include "ruperts/tubetree229.h"
#include "ruperts/nopert231.h"
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

  std::cout << "Outer hull vertices at Corner 2 (" << H << " vertices):\n";
  for (int h : hull) {
    std::cout << "  v" << h << ": (" << outer_pts[h].x << ", " << outer_pts[h].y << ")\n";
  }

  // Check the unconstrained direction: rotation -omega
  // For each vertex k in the inner polyhedron, rotated by theta around -omega:
  // R(theta, -omega) * v_k
  for (double theta : {1e-7, 1e-6, 1e-5, 1e-4}) {
    // Rotation matrix around -omega:
    vec3 w = -omega;
    // v_rot = v + sin(theta) * (w x v) + (1 - cos(theta)) * (w x (w x v))
    // We want to find translation t in R^2 that minimizes the maximum penetration
    // outside the outer hull halfspaces.
    // Outer halfspaces: for each edge (hull[i], hull[i+1]):
    // inward/outward normal
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

    // Inner vertices rotated:
    std::vector<vec2> inner_pts(NUM_VERTICES);
    for (int k = 0; k < NUM_VERTICES; k++) {
      vec3 v = Vertex(k);
      vec3 v_rot = v + std::sin(theta) * yocto::cross(w, v) + (1.0 - std::cos(theta)) * yocto::cross(w, yocto::cross(w, v));
      inner_pts[k] = vec2{yocto::dot(v_rot, first), yocto::dot(v_rot, second)};
    }

    // Grid search for optimal translation t that minimizes max_k max_i (n_i . (inner_pts[k] + t) - offsets[i])
    double best_max_pen = 1e9;
    vec2 best_t = {0, 0};
    for (double tx = -2 * theta; tx <= 2 * theta; tx += theta / 50.0) {
      for (double ty = -2 * theta; ty <= 2 * theta; ty += theta / 50.0) {
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
    std::cout << "theta = " << std::scientific << theta
              << ": best translation t = (" << best_t.x << ", " << best_t.y << ")"
              << ", min-max penetration = " << best_max_pen << "\n";
  }

  return 0;
}
