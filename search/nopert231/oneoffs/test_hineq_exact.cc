#include <iostream>
#include <iomanip>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

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

  ContactInfo c_core[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 center_core;
  BigRat delta_core;
  Tube229::AuditAxis(tri, c_core, &ax_core, &center_core, &delta_core, &err, BigRat(5, 1000));

  BigVecQ3 u = center0 / ax0.B;
  BigVecQ3 v = center_core / ax_core.B;

  BigRat A = u.x * u.x + u.y * u.y + u.z * u.z;
  BigRat u_dot_v = u.x * v.x + u.y * v.y + u.z * v.z;
  BigRat lam = u_dot_v / A;
  BigVecQ3 w = {v.x - lam * u.x, v.y - lam * u.y, v.z - lam * u.z};
  BigRat B_w = w.x * w.x + w.y * w.y + w.z * w.z;

  std::cout << std::setprecision(10);
  std::cout << "A (||u||^2) = " << A.ToDouble() << "\n";
  std::cout << "||u|| = " << std::sqrt(A.ToDouble()) << "\n";
  std::cout << "B_w (||w||^2) = " << B_w.ToDouble() << "\n";
  std::cout << "lam = " << lam.ToDouble() << "\n";
  std::cout << "u_dot_v = " << u_dot_v.ToDouble() << "\n";

  BigRat c_core(3, 10000);

  for (double cc = 0.015; cc <= 0.045; cc += 0.002) {
    BigRat c_cone(std::round(cc * 10000), 10000);
    BigRat margin = lam * c_cone - c_core;
    BigRat lhs = B_w * (A - c_cone * c_cone);
    BigRat rhs = A * margin * margin;
    std::cout << "c_cone = " << cc << " -> lhs=" << lhs.ToDouble()
              << ", rhs=" << rhs.ToDouble()
              << ", diff(rhs-lhs)=" << (rhs - lhs).ToDouble() << "\n";
  }

  return 0;
}
