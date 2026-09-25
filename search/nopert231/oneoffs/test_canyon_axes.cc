#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string path = "03121303021";
  TriangleQ tri = TriangleFromPath(path);
  std::cout << "Analyzing triangle " << path << "...\n";

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Found " << axes.size() << " audited hull support axes.\n";

  std::ofstream out("canyon_axes_centers.txt");
  for (const auto &ax : axes) {
    vec3 c = ToVec3(ax.center);
    out << c.x << " " << c.y << " " << c.z << "\n";
  }

  return 0;
}
