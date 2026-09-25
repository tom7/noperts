#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  // We know axes[24] and axes[210] are great:
  const auto &ax2 = axes[24];
  const auto &ax3 = axes[210];
  std::cout << "ax2 delta = " << ax2.delta.ToDouble() << "\n";
  std::cout << "ax3 delta = " << ax3.delta.ToDouble() << "\n";

  double c_cone = 0.017;

  int count = 0;
  for (size_t i = 0; i < axes.size(); i++) {
    const auto &ax1 = axes[i];
    if (ax1.delta.ToDouble() > 0.000180) continue;

    // Check if {ax1, ax2, ax3} form a valid complement cage circumscribing the target at c_cone
    // In our formulation, the target octahedron vertices have to be strictly inside the positive cone of (u0, u1, u2).
    // Specifically, every octahedron vertex + c_cone * e_i must have positive barycentric coordinates with positive margin.
    double B1 = ax1.cert.B.ToDouble();
    double B2 = ax2.cert.B.ToDouble();
    double B3 = ax3.cert.B.ToDouble();
    vec3 u1 = vec3{ax1.center.x.ToDouble() / B1, ax1.center.y.ToDouble() / B1, ax1.center.z.ToDouble() / B1};
    vec3 u2 = vec3{ax2.center.x.ToDouble() / B2, ax2.center.y.ToDouble() / B2, ax2.center.z.ToDouble() / B2};
    vec3 u3 = vec3{ax3.center.x.ToDouble() / B3, ax3.center.y.ToDouble() / B3, ax3.center.z.ToDouble() / B3};

    // det(u1, u2, u3)
    double det = yocto::dot(u1, yocto::cross(u2, u3));
    if (det <= 1e-6) continue;

    // Invert matrix [u1 u2 u3]
    vec3 row1 = yocto::cross(u2, u3) / det;
    vec3 row2 = yocto::cross(u3, u1) / det;
    vec3 row3 = yocto::cross(u1, u2) / det;

    bool valid = true;
    double min_bary = 1e9;
    // 6 octahedron vertices: +/- e_x, +/- e_y, +/- e_z
    vec3 oct[6] = {
      {1, 0, 0}, {-1, 0, 0},
      {0, 1, 0}, {0, -1, 0},
      {0, 0, 1}, {0, 0, -1}
    };
    for (int v = 0; v < 6; v++) {
      // test target point oct[v] - c_cone * (oct[v]) or similar:
      // In the flock theorem, the target was:
      // for all adversary points outside the cone <a, u0> < c_cone,
      // <a, u_i> >= 0 for at least one cage axis.
      // That is: the dual cone of {u1, u2, u3} circumscribes the complement of the cone!
    }
  }

  return 0;
}
