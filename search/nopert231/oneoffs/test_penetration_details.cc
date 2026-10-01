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
  vec3 w = -omega;

  double theta = 1e-5;
  vec2 t = {-1.2e-6, 4.4e-6};

  std::vector<vec2> normals(H);
  std::vector<double> offsets(H);
  for (int i = 0; i < H; i++) {
    int v0 = hull[i];
    int v1 = hull[(i + 1) % H];
    vec2 edge = outer_pts[v1] - outer_pts[v0];
    vec2 n = vec2{edge.y, -edge.x};
    n = n / yocto::length(vec3{n.x, n.y, 0});
    normals[i] = n;
    offsets[i] = normals[i].x * outer_pts[v0].x + normals[i].y * outer_pts[v0].y;
  }

  std::cout << "Penetrations for theta = " << theta << ", t = (" << t.x << ", " << t.y << "):\n";
  for (int k = 0; k < NUM_VERTICES; k++) {
    vec3 v = Vertex(k);
    vec3 v_rot = v + std::sin(theta) * yocto::cross(w, v) + (1.0 - std::cos(theta)) * yocto::cross(w, yocto::cross(w, v));
    vec2 p = vec2{yocto::dot(v_rot, first), yocto::dot(v_rot, second)} + t;
    for (int i = 0; i < H; i++) {
      double pen = normals[i].x * p.x + normals[i].y * p.y - offsets[i];
      if (pen > 1e-9) {
        std::cout << "  Vertex v" << k << " penetrates edge (" << hull[i] << "->" << hull[(i+1)%H] << ") by " << pen << "\n";
      }
    }
  }

  return 0;
}
