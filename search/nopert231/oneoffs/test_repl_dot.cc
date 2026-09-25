#include <iostream>
#include <iomanip>
#include <cmath>

struct vec3 { double x, y, z; };
double dot(vec3 a, vec3 b) { return a.x*b.x + a.y*b.y + a.z*b.z; }

int main() {
  vec3 norm_a = {0.0405068923243, 0.0610180604041, 0.0389051544149};
  vec3 uncov = {0.401011, -0.483067, -0.778355};
  double l = std::sqrt(dot(uncov, uncov));
  uncov = {uncov.x/l, uncov.y/l, uncov.z/l};

  std::cout << std::setprecision(10);
  std::cout << "dot(norm_a, uncov) = " << dot(norm_a, uncov) << "\n";
  std::cout << "dot(norm_a, -uncov) = " << dot(norm_a, {-uncov.x, -uncov.y, -uncov.z}) << "\n";
  return 0;
}
