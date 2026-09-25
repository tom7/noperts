#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // Axis 0:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  // Core axis:
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &center_core, &delta_core, &err, BigRat(0));
  vec3 v_core = {center_core.x.ToDouble() / ax_core.B.ToDouble(),
                 center_core.y.ToDouble() / ax_core.B.ToDouble(),
                 center_core.z.ToDouble() / ax_core.B.ToDouble()};

  // We had 8 selected complement axes:
  // Let's see the angle of the worst remaining point to u0 and to v_core:
  // In Round 4: min_u0 = 0.0192517 (norm(u0) = 0.0511, so cos(theta) = 0.01925 / 0.0511 = 0.376 -> theta = 67.8 degrees)
  // v_core is at 37 degrees from u0.
  // What is the direction of (u0 + v_core) / 2?
  vec3 mid = yocto::normalize(u0 + v_core);
  std::cout << "Angle between u0 and v_core: "
            << (std::acos(yocto::dot(yocto::normalize(u0), yocto::normalize(v_core))) * 180.0 / M_PI) << " deg\n";

  // Can we define a second core axis v_core2?
  // Let's test if there is ANOTHER zero-defect axis that covers the negative region of v_core!
  // What if we have TWO core axes for the inner core?
  // If we have TWO core axes v_core1 and v_core2:
  // For small angles theta <= r_min, every point in the cone has EITHER
  // dot(a, v_core1) >= c_core OR dot(a, v_core2) >= c_core!

  return 0;
}
