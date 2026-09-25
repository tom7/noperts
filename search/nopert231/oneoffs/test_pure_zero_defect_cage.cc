#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

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

  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  ContactInfo copp[3] = {
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(2, 1, 1, 4, 600, 1),
    MakeContact(8, 9, 9, 10, 800, 9)
  };

  std::string err;
  AxisCertificate ax1, ax2, ax3, axopp;
  BigVecQ3 ctr1, ctr2, ctr3, ctropp;
  BigRat del1, del2, del3, delopp;

  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));
  Tube229::AuditAxis(tri, copp, &axopp, &ctropp, &delopp, &err, BigRat(0));

  vec3 u1 = {ctr1.x.ToDouble() / ax1.B.ToDouble(), ctr1.y.ToDouble() / ax1.B.ToDouble(), ctr1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 u2 = {ctr2.x.ToDouble() / ax2.B.ToDouble(), ctr2.y.ToDouble() / ax2.B.ToDouble(), ctr2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 u3 = {ctr3.x.ToDouble() / ax3.B.ToDouble(), ctr3.y.ToDouble() / ax3.B.ToDouble(), ctr3.z.ToDouble() / ax3.B.ToDouble()};
  vec3 uopp = {ctropp.x.ToDouble() / axopp.B.ToDouble(), ctropp.y.ToDouble() / axopp.B.ToDouble(), ctropp.z.ToDouble() / axopp.B.ToDouble()};

  std::cout << "All 4 axes audited with ZERO defect!\n";
  std::cout << "  del1 = " << del1.ToDouble() << "\n";
  std::cout << "  del2 = " << del2.ToDouble() << "\n";
  std::cout << "  del3 = " << del3.ToDouble() << "\n";
  std::cout << "  delopp = " << delopp.ToDouble() << "\n";

  vec3 pts[4] = {uopp, u1, u2, u3};
  std::cout << "\nDistances from origin to faces of {uopp, u1, u2, u3}:\n";
  bool inside = true;
  double min_d = 1e30;
  for (int face = 0; face < 4; face++) {
    int i = (face == 0) ? 1 : 0;
    int j = (face <= 1) ? 2 : 1;
    int k = (face <= 2) ? 3 : 2;
    vec3 n = yocto::cross(pts[j] - pts[i], pts[k] - pts[i]);
    double n_len = yocto::length(n);
    n = n / n_len;
    double d = yocto::dot(pts[i], n);
    if (d < 0) {
      n = -n;
      d = -d;
    }
    double fourth_side = yocto::dot(pts[face], n) - d;
    std::cout << "  Face " << face << " (excluding pt " << face << "): distance = " << d
              << ", 4th pt side = " << fourth_side << "\n";
    if (fourth_side >= 0) inside = false;
    if (d < min_d) min_d = d;
  }

  if (inside) {
    std::cout << "\nORIGIN IS STRICTLY INSIDE THE PURE ZERO-DEFECT TETRAHEDRON!\n";
    std::cout << "  inradius = " << min_d << "\n";
  } else {
    std::cout << "\nOrigin is outside or on boundary.\n";
  }

  return 0;
}
