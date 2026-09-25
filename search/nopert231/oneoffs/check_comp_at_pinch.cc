#include <iostream>
#include <vector>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble(), ctr0.y.ToDouble(), ctr0.z.ToDouble()});
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double x = 1.265142, y = -0.9695975;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  // Complement axes from print_lean_decomposed_row:
  ContactInfo c1[3] = {
    MakeContact(18, 1, 1, 5, 200, 1),
    MakeContact(9, 10, 10, 15, 270, 10),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo c2[3] = {
    MakeContact(15, 19, 19, 3, 290, 19),
    MakeContact(5, 8, 8, 9, 600, 8),
    MakeContact(15, 19, 19, 3, 600, 19)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 130, 2),
    MakeContact(2, 1, 1, 5, 420, 1),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  AxisCertificate ax[3];
  BigVecQ3 ctr[3];
  BigRat del[3];
  Tube229::AuditAxis(tri, c1, &ax[0], &ctr[0], &del[0], &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax[1], &ctr[1], &del[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax[2], &ctr[2], &del[2], &err, BigRat(0));

  std::cout << "Pinch point p: dot(p, u0) = " << yocto::dot(p, u0) << "\n";
  for (int j = 0; j < 3; j++) {
    vec3 v = yocto::normalize(vec3{ctr[j].x.ToDouble(), ctr[j].y.ToDouble(), ctr[j].z.ToDouble()});
    std::cout << "  dot(p, comp[" << j+1 << "]) = " << yocto::dot(p, v) << "\n";
  }

  return 0;
}
