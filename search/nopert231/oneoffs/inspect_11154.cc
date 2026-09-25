#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

// Copy minimal types from lean229.cc
struct vec3 { double x, y, z; };
inline vec3 cross(vec3 a, vec3 b) {
  return {a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x};
}
inline double dot(vec3 a, vec3 b) {
  return a.x*b.x + a.y*b.y + a.z*b.z;
}

int main() {
  std::cout << "Testing pool triple 11154...\n";
  return 0;
}
