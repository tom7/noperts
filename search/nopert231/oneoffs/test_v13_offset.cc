#include <iostream>
#include <iomanip>
#include "ruperts/tubetree229.h"
#include "ruperts/nopert231.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main() {
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");
  vec3 c2 = {tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()};
  vec3 u = yocto::normalize(c2);
  vec3 axis = {0, 1, 0};
  vec3 ex = yocto::normalize(yocto::cross(u, axis));
  vec3 ey = yocto::cross(u, ex);

  auto proj = [&](vec3 v) -> Tube229::vec2 { return {yocto::dot(v, ex), yocto::dot(v, ey)}; };

  Tube229::vec2 p10 = proj(Vertex(10));
  Tube229::vec2 p15 = proj(Vertex(15));
  Tube229::vec2 p13 = proj(Vertex(13));

  Tube229::vec2 edge = p15 - p10;
  Tube229::vec2 n = {edge.y, -edge.x};
  double l = std::sqrt(n.x*n.x + n.y*n.y);
  n = {n.x / l, n.y / l};

  std::cout << std::setprecision(10);
  std::cout << "p10 = (" << p10.x << ", " << p10.y << ")\n";
  std::cout << "p15 = (" << p15.x << ", " << p15.y << ")\n";
  std::cout << "p13 = (" << p13.x << ", " << p13.y << ")\n";
  std::cout << "n = (" << n.x << ", " << n.y << ")\n";

  double offset10 = n.x * p10.x + n.y * p10.y;
  double offset13 = n.x * p13.x + n.y * p13.y;
  std::cout << "dot(n, p10) = " << offset10 << "\n";
  std::cout << "dot(n, p13) = " << offset13 << "\n";
  std::cout << "pen(v13) at theta=0 = dot(n, p13 - p10) = " << (offset13 - offset10) << "\n";

  return 0;
}
