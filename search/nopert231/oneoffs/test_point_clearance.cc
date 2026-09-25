#include <iostream>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  vec3 a = {0.306184, -0.727484, -0.614018};
  // Normalize a:
  a = yocto::normalize(a);

  // Let's test a sample of rotation angles theta in [0, 1/500]:
  // For small theta, R = I + sin(theta) [a]_x + (1 - cos(theta)) [a]_x^2
  // We check which contact edges/vertices provide positive clearance.
  std::cout << "Testing axis a = (" << a.x << ", " << a.y << ", " << a.z << ")\n";

  // Check 2D projected convex hull of polyhedron rotated by R(a, theta)
  // versus the outer polyhedron profile.
  // We can just audit all possible contacts for this direction!
  // In fact, let's find the best hull support axis for direction a:
  tubetree229::AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  std::string err;
  bool ok = Tube229::FindHullSupportAxis(tri, &cert, &center, &delta, &err);
  if (ok) {
    std::cout << "FindHullSupportAxis succeeded! delta = " << delta.ToDouble() << "\n";
  } else {
    std::cout << "FindHullSupportAxis failed: " << err << "\n";
  }


  return 0;
}
