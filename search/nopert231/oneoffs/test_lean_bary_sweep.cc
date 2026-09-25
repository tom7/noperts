#include <iostream>
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

static BigRat Det3(const BigVecQ3 &a, const BigVecQ3 &b, const BigVecQ3 &c) {
  return BigVecQ3::Dot(a, BigVecQ3::Cross(b, c));
}

static bool CheckBarycentric(const BigVecQ3 p[4], const BigVecQ3 &target) {
  BigVecQ3 a = p[0] - p[3];
  BigVecQ3 b = p[1] - p[3];
  BigVecQ3 c = p[2] - p[3];
  BigVecQ3 y = target - p[3];

  BigRat D = Det3(a, b, c);
  if (D == 0) return false;

  BigRat l0 = Det3(y, b, c) / D;
  BigRat l1 = Det3(a, y, c) / D;
  BigRat l2 = Det3(a, b, y) / D;
  BigRat l3 = BigRat(1) - l0 - l1 - l2;

  return (l0 >= 0 && l1 >= 0 && l2 >= 0 && l3 >= 0);
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo contacts[4][3] = {
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(2, 1, 1, 4, 333, 1) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 666, 15), MakeContact(3, 2, 2, 1, 0, 2) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(1, 4, 4, 8, 333, 4), MakeContact(15, 19, 19, 3, 1000, 19) }
  };

  BigVecQ3 ctr[4];
  AxisCertificate ax[4];
  BigRat del[4];
  std::string err;

  for (int j = 0; j < 4; j++) {
    bool ok = Tube229::AuditAxis(tri, contacts[j], &ax[j], &ctr[j], &del[j], &err, BigRat(5, 1000));
    if (!ok) return 1;
  }

  BigRat box_delta(234013, 1000000000LL);

  for (int c_cone_int : {5, 8, 10, 12, 15, 17, 20}) {
    BigRat c_cone(c_cone_int, 1000);
    for (int c_int : {240, 250, 260, 280, 300, 350, 400, 500, 1000}) {
      BigRat c_val(c_int, 1000000);
      BigRat scale = (c_val + box_delta) / c_cone;
      BigRat oct_radius = BigRat(7, 4) * (c_val + box_delta);

      BigVecQ3 oct[6] = {
        BigVecQ3(oct_radius, BigRat(0), BigRat(0)),
        BigVecQ3(-oct_radius, BigRat(0), BigRat(0)),
        BigVecQ3(BigRat(0), oct_radius, BigRat(0)),
        BigVecQ3(BigRat(0), -oct_radius, BigRat(0)),
        BigVecQ3(BigRat(0), BigRat(0), oct_radius),
        BigVecQ3(BigRat(0), BigRat(0), -oct_radius),
      };

      BigVecQ3 p[4];
      p[0] = ctr[0] * scale;
      p[1] = ctr[1];
      p[2] = ctr[2];
      p[3] = ctr[3];

      bool all_oct_ok = true;
      for (int k = 0; k < 6; k++) {
        if (!CheckBarycentric(p, oct[k])) {
          all_oct_ok = false;
          break;
        }
      }
      if (all_oct_ok) {
        std::cout << "OK: c_cone = " << c_cone_int << "/1000, c = " << c_int << "/1000000\n";
      }
    }
  }
  return 0;
}
