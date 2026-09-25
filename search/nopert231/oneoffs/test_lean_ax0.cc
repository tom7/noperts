#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  // Exact mix from test_full_box_03121303200.lean:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  double norm_u0 = yocto::length(u0);
  vec3 u0_unit = yocto::normalize(u0);

  std::cout << "Lean ax0 center: " << u0.x << ", " << u0.y << ", " << u0.z << "\n";
  std::cout << "norm(u0) = " << norm_u0 << "\n";
  std::cout << "B = " << ax0.B.ToDouble() << "\n";

  // Check what Lean's coreAxis is:
  // def coreAxis : AxisCertificate := {
  //   edgeStart := ![1, 10, 10], edgeFinish := ![4, 15, 15], edgeStart₂ := ![4, 15, 15], edgeFinish₂ := ![8, 19, 19],
  //   mix := ![1000, 400, 0], index := ![4, 15, 15]
  ContactInfo c_core[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  vec3 v_core = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.z.ToDouble() / ax_core.B.ToDouble()};
  std::cout << "Lean coreAxis center: " << v_core.x << ", " << v_core.y << ", " << v_core.z << "\n";
  std::cout << "dot(u0_unit, v_core) = " << yocto::dot(u0_unit, v_core) << "\n";

  return 0;
}
