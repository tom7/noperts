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

  // Annular axis:
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

  // inner_core_axis stored in tree_0.json:
  ContactInfo c_core[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(14, 15, 15, 19, 500, 15),
    MakeContact(2, 1, 1, 4, 500, 1)
  };
  AxisCertificate ax_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  bool ok = Tube229::AuditAxis(tri, c_core, &ax_core, &center_core, &delta_core, &err, BigRat(0));
  std::cout << "AuditAxis on stored inner_core_axis: " << (ok ? "SUCCESS" : ("FAIL: " + err)) << "\n";
  if (ok) {
    vec3 v_core = {center_core.x.ToDouble() / ax_core.B.ToDouble(),
                   center_core.y.ToDouble() / ax_core.B.ToDouble(),
                   center_core.z.ToDouble() / ax_core.B.ToDouble()};
    std::cout << "v_core: (" << v_core.x << ", " << v_core.y << ", " << v_core.z << ") len=" << yocto::length(v_core) << "\n";
    std::cout << "u0: (" << u0.x << ", " << u0.y << ", " << u0.z << ") len=" << yocto::length(u0) << "\n";

    double ang = std::acos(yocto::dot(yocto::normalize(u0), yocto::normalize(v_core))) * 180.0 / M_PI;
    std::cout << "Angle between u0 and stored v_core: " << ang << " degrees\n";
  }

  return 0;
}
