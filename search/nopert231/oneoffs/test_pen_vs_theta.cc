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

  // Find index of edge 10->15
  int edge_10_15 = -1;
  for (int i = 0; i < H; i++) {
    if (hull[i] == 10 && hull[(i+1)%H] == 15) edge_10_15 = i;
  }
  std::cout << "Edge 10->15 is hull index: " << edge_10_15 << "\n";
  std::cout << "At theta = 0, t = 0: pen(v13) = "
            << normals[edge_10_15].x * outer_pts[13].x + normals[edge_10_15].y * outer_pts[13].y - offsets[edge_10_15] << "\n";

  return 0;
}
