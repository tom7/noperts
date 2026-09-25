#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Total axes found: " << axes.size() << "\n";

  vec3 p1 = {14.3165, -17.5138, -28.486};
  double len = yocto::length(p1);
  vec3 a1 = p1 / len;

  int count = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    vec3 v = vec3{axes[i].center.x.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.y.ToDouble() / axes[i].cert.B.ToDouble(),
                  axes[i].center.z.ToDouble() / axes[i].cert.B.ToDouble()};
    double d = yocto::dot(a1, v);
    if (d >= 0.0005) {
      count++;
      if (count <= 10) {
        std::cout << "Covered by axis " << i << " with dot=" << d << ", delta=" << axes[i].delta.ToDouble() << "\n";
      }
    }
  }
  std::cout << "Total covering axes for p1: " << count << "\n";
  return 0;
}
