#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 6000);

  auto PrintV = [&](const std::string &name, const Tube229::AuditedAxis &ax) {
    vec3 v = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    std::cout << name << ": |v| = " << yocto::length(v)
              << ", delta = " << ax.delta.ToDouble()
              << ", B = " << ax.cert.B.ToDouble()
              << ", v = (" << v.x << ", " << v.y << ", " << v.z << ")\n";
  };

  PrintV("Axis 22", axes[22]);
  PrintV("Axis 23", axes[23]);
  PrintV("Axis 5293", axes[5293]);

  return 0;
}
