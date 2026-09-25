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
  c.edge_start = start;
  c.edge_finish = finish;
  c.edge_start2 = start2;
  c.edge_finish2 = finish2;
  c.mix = mix;
  c.vertex = v;
  return c;
}

static BigRat det3Q(const BigVecQ3 &u, const BigVecQ3 &v, const BigVecQ3 &w) {
  return u.x * (v.y * w.z - v.z * w.y) -
         u.y * (v.x * w.z - v.z * w.x) +
         u.z * (v.x * w.y - v.y * w.x);
}

static bool tetraBarycentricQ(const BigVecQ3 p[4], const BigVecQ3 &target, BigRat bary[4]) {
  BigVecQ3 a = p[0] - p[3];
  BigVecQ3 b = p[1] - p[3];
  BigVecQ3 c = p[2] - p[3];
  BigVecQ3 y = target - p[3];
  BigRat D = det3Q(a, b, c);
  if (BigRat::Sign(D) == 0) return false;
  BigRat l0 = det3Q(y, b, c) / D;
  BigRat l1 = det3Q(a, y, c) / D;
  BigRat l2 = det3Q(a, b, y) / D;
  bary[0] = l0;
  bary[1] = l1;
  bary[2] = l2;
  bary[3] = BigRat(1) - l0 - l1 - l2;
  return true;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
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

  std::string err;
  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 ctr0, ctr1, ctr2, ctr3;
  BigRat del0, del1, del2, del3;

  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  BigRat delta = del0;
  if (del1 > delta) delta = del1;
  if (del2 > delta) delta = del2;
  if (del3 > delta) delta = del3;

  BigVecQ3 u0 = ctr0 / ax0.B;
  BigVecQ3 u1 = ctr1 / ax1.B;
  BigVecQ3 u2 = ctr2 / ax2.B;
  BigVecQ3 u3 = ctr3 / ax3.B;

  BigRat c_cone(65, 1000);

  std::cout << "delta = " << delta.ToDouble() << "\n";

  for (double c_val = 0.005; c_val >= 0.00001; c_val -= 0.0001) {
    BigRat c = BigRat::FromDouble(c_val);
    BigVecQ3 v0 = u0 * (c / c_cone);
    BigVecQ3 tet[4] = {v0, u1, u2, u3};

    BigRat oct_rad = (c + delta) * BigRat(7, 4);

    bool all_ok = true;
    for (int k = 0; k < 6; k++) {
      BigVecQ3 target{BigRat(0), BigRat(0), BigRat(0)};
      BigRat s = (k % 2 == 0) ? oct_rad : (BigRat(0) - oct_rad);
      if (k / 2 == 0) target.x = s;
      else if (k / 2 == 1) target.y = s;
      else target.z = s;

      BigRat bary[4];
      if (!tetraBarycentricQ(tet, target, bary)) {
        all_ok = false;
        break;
      }
      for (int j = 0; j < 4; j++) {
        if (BigRat::Sign(bary[j]) < 0) {
          all_ok = false;
          break;
        }
      }
      if (!all_ok) break;
    }

    if (all_ok) {
      std::cout << "SUCCESS at c = " << c_val << " (c + delta = " << (c + delta).ToDouble()
                << ", oct_rad = " << oct_rad.ToDouble() << ")\n";
      return 0;
    }
  }

  std::cout << "No c found for octahedron enclosure.\n";
  return 0;
}
