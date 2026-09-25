#include <iostream>
#include <string>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"
#include "bignum/big-vec.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

static BigRat det3Q(const BigVecQ3 &u, const BigVecQ3 &v, const BigVecQ3 &w) {
  return u.x * (v.y * w.z - v.z * w.y) -
         u.y * (v.x * w.z - v.z * w.x) +
         u.z * (v.x * w.y - v.y * w.x);
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

  BigVecQ3 u1 = ctr1 / ax1.B;
  BigVecQ3 u2 = ctr2 / ax2.B;
  BigVecQ3 u3 = ctr3 / ax3.B;
  BigVecQ3 uopp = ctropp / axopp.B;

  BigVecQ3 p[4] = {uopp, u1, u2, u3};
  BigVecQ3 a = p[0] - p[3];
  BigVecQ3 b = p[1] - p[3];
  BigVecQ3 c = p[2] - p[3];
  BigVecQ3 y = BigVecQ3(BigRat(0), BigRat(0), BigRat(0)) - p[3];

  BigRat D = det3Q(a, b, c);
  BigRat l0 = det3Q(y, b, c) / D;
  BigRat l1 = det3Q(a, y, c) / D;
  BigRat l2 = det3Q(a, b, y) / D;
  BigRat l3 = BigRat(1) - l0 - l1 - l2;

  std::cout << "Barycentric coordinates of origin in {uopp, u1, u2, u3}:\n";
  std::cout << "  l0 (uopp) = " << l0.ToDouble() << "\n";
  std::cout << "  l1 (u1)   = " << l1.ToDouble() << "\n";
  std::cout << "  l2 (u2)   = " << l2.ToDouble() << "\n";
  std::cout << "  l3 (u3)   = " << l3.ToDouble() << "\n";

  return 0;
}
