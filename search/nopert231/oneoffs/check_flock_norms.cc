#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // Flock axes indices: 0, 1, 4
  int idx[] = {0, 1, 4};
  for (int m = 0; m < 3; m++) {
    int i = idx[m];
    double B = axes[i].cert.B.ToDouble();
    vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
    std::cout << "Flock " << m << " (axis " << i << "): length = " << yocto::length(v)
              << ", B = " << B << ", delta = " << axes[i].delta.ToDouble() << "\n";
  }
  return 0;
}
