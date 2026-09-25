#include <iostream>
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
  std::string path = "03121300";
  TriangleQ tri = TriangleFromPath(path);
  ContactInfo core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_new;
  BigVecQ3 ctr_new;
  BigRat del_new;
  std::string err;
  Tube229::AuditAxis(tri, core, &ax_new, &ctr_new, &del_new, &err, BigRat(0));

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(5, 1000));

  vec3 u_new = {ctr_new.x.ToDouble() / ax_new.B.ToDouble(),
                ctr_new.y.ToDouble() / ax_new.B.ToDouble(),
                ctr_new.z.ToDouble() / ax_new.B.ToDouble()};
  vec3 u_ann = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
                ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
                ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};

  double dot = yocto::dot(yocto::normalize(u_new), yocto::normalize(u_ann));
  double ang = std::acos(std::clamp(dot, -1.0, 1.0)) * 180.0 / M_PI;
  std::cout << "Angle between zero-defect axis and ax_ann: " << ang << " deg\n";
  std::cout << "del_new = " << del_new.ToDouble() << ", B_new = " << ax_new.B.ToDouble() << "\n";
  return 0;
}
