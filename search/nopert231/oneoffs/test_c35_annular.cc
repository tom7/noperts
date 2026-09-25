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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 800, 15) // zero defect!
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  bool ok0 = Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0));
  std::cout << "c35 audited with zero defect? " << (ok0 ? "YES" : "NO: " + err) << "\n";

  // Can complement axes 1, 2, 3 cage c35?
  // Axes 1, 2, 3 from print_lean_decomposed_row:
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

  AxisCertificate ax1, ax2, ax3;
  BigVecQ3 ctr1, ctr2, ctr3;
  BigRat del1, del2, del3;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  // Check octahedral barycentric coverage with ax0, ax1, ax2, ax3
  std::vector<vec3> comp_pts = {
    vec3{ctr1.x.ToDouble() / ax1.B.ToDouble(), ctr1.y.ToDouble() / ax1.B.ToDouble(), ctr1.z.ToDouble() / ax1.B.ToDouble()},
    vec3{ctr2.x.ToDouble() / ax2.B.ToDouble(), ctr2.y.ToDouble() / ax2.B.ToDouble(), ctr2.z.ToDouble() / ax2.B.ToDouble()},
    vec3{ctr3.x.ToDouble() / ax3.B.ToDouble(), ctr3.y.ToDouble() / ax3.B.ToDouble(), ctr3.z.ToDouble() / ax3.B.ToDouble()}
  };
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};

  std::cout << "u0 = (" << u0.x << ", " << u0.y << ", " << u0.z << "), norm = " << yocto::length(u0) << "\n";
  for (int j = 0; j < 3; j++) {
    std::cout << "comp[" << j+1 << "] = (" << comp_pts[j].x << ", " << comp_pts[j].y << ", " << comp_pts[j].z
              << "), dot(u0, comp) = " << yocto::dot(u0, comp_pts[j]) << "\n";
  }

  return 0;
}
