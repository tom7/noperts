#include <iostream>
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

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 150, 2),
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(13, 14, 14, 15, 882, 14)
  };
  ContactInfo c_core[3] = {
    MakeContact(3, 2, 2, 1, 600, 2),
    MakeContact(1, 4, 4, 8, 400, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };

  std::string err;
  AxisCertificate ax0, ax_core;
  BigVecQ3 ctr0, ctr_core;
  BigRat del0, del_core;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  bool ok = Tube229::AuditAxis(tri, c_core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));

  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 uc = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
             ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
             ctr_core.z.ToDouble() / ax_core.B.ToDouble()};

  double dot = yocto::dot(yocto::normalize(u0), yocto::normalize(uc));
  double angle = std::acos(std::max(-1.0, std::min(1.0, dot))) * 180.0 / M_PI;
  std::cout << "Audit core ok: " << ok << ", del_core = " << del_core.ToDouble() << "\n";
  std::cout << "Angle between u0 and uc = " << angle << " degrees (dot = " << dot << ")\n";
  std::cout << "|u0| = " << yocto::length(u0) << ", |uc| = " << yocto::length(uc) << "\n";
  return 0;
}
