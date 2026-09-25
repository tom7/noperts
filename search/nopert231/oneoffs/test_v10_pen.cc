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

  vec3 omega = yocto::normalize(vec3{-0.400992, 0.483041, 0.778381});
  vec3 w = -omega;

  vec2 edge = outer_pts[15] - outer_pts[10];
  vec2 n = vec2{edge.y, -edge.x};
  n = n / yocto::length(vec3{n.x, n.y, 0});
  double offset = n.x * outer_pts[10].x + n.y * outer_pts[10].y;

  double theta = 1e-5;
  vec2 best_t = {1.699e-06, -1.404e-06};

  for (int k : {10, 13, 14, 15}) {
    vec3 v = Vertex(k);
    vec3 v_rot = v + std::sin(theta) * yocto::cross(w, v) + (1.0 - std::cos(theta)) * yocto::cross(w, yocto::cross(w, v));
    vec2 p = vec2{yocto::dot(v_rot, first), yocto::dot(v_rot, second)} + best_t;
    double pen = n.x * p.x + n.y * p.y - offset;
    std::cout << "v" << k << " pen at best_t: " << pen << " (rate: " << pen / theta << ")\n";
  }

  return 0;
}
