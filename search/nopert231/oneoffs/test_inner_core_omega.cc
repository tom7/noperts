#include <iostream>
#include <string>
#include <vector>
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

int main() {
  vec3 omega_obs = {-0.400992, 0.483041, 0.778381};
  std::cout << "Obstruction direction -omega: (" << -omega_obs.x << ", " << -omega_obs.y << ", " << -omega_obs.z << ")\n";

  TriangleQ tri = TriangleFromPath("3121300");
  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  std::string fail;
  if (Tube229::FindHullSupportAxis(tri, &cert, &center, &delta, &fail)) {
    vec3 c = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
    vec3 u = yocto::normalize(c);
    std::cout << "Path 3121300 inner_core_axis:\n";
    std::cout << "  center: (" << c.x << ", " << c.y << ", " << c.z << ")\n";
    std::cout << "  normalized: (" << u.x << ", " << u.y << ", " << u.z << ")\n";
    std::cout << "  dot(u, -omega_obs): " << yocto::dot(u, -omega_obs) << "\n";
    std::cout << "  dot(u,  omega_obs): " << yocto::dot(u,  omega_obs) << "\n";
  }

  // Also test path 3121303021
  TriangleQ tri2 = TriangleFromPath("3121303021");
  if (Tube229::FindHullSupportAxis(tri2, &cert, &center, &delta, &fail)) {
    vec3 c = {center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()};
    vec3 u = yocto::normalize(c);
    std::cout << "\nPath 3121303021 inner_core_axis:\n";
    std::cout << "  center: (" << c.x << ", " << c.y << ", " << c.z << ")\n";
    std::cout << "  normalized: (" << u.x << ", " << u.y << ", " << u.z << ")\n";
    std::cout << "  dot(u, -omega_obs): " << yocto::dot(u, -omega_obs) << "\n";
    std::cout << "  dot(u,  omega_obs): " << yocto::dot(u,  omega_obs) << "\n";
  }

  return 0;
}
