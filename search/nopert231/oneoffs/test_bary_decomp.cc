#include <iostream>
#include <vector>
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

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  // Annular axes from TestEvalRealCage.lean:
  ContactInfo cts[4][3] = {
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14) },
    { MakeContact(15, 19, 19, 3, 200, 19), MakeContact(2, 1, 1, 4, 200, 1), MakeContact(8, 9, 9, 10, 200, 9) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15) },
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(4, 8, 8, 9, 800, 8), MakeContact(14, 15, 15, 19, 800, 15) }
  };

  BigVecQ3 ctr[4];
  BigRat B[4];
  BigRat del[4];
  std::string err;
  for (int j = 0; j < 4; j++) {
    AxisCertificate ax;
    Tube229::AuditAxis(tri, cts[j], &ax, &ctr[j], &del[j], &err, j == 0 ? BigRat(5, 1000) : BigRat(0));
    B[j] = ax.B;
  }

  BigVecQ3 norm_ctr[4];
  for (int j = 0; j < 4; j++) {
    norm_ctr[j] = BigVecQ3{BigRat::Div(ctr[j].x, B[j]),
                           BigRat::Div(ctr[j].y, B[j]),
                           BigRat::Div(ctr[j].z, B[j])};
  }

  BigRat delta = BigRat(260, 1000000);

  for (double c_val : {0.000265, 0.000280, 0.000300, 0.001000}) {
    BigRat c = BigRat(std::round(c_val * 1000000), 1000000);
    for (double c_cone_val : {0.015, 0.020, 0.025}) {
      BigRat c_cone = BigRat(std::round(c_cone_val * 1000), 1000);

      BigRat scale0 = BigRat::Div(BigRat::Plus(c, delta), c_cone);
      BigVecQ3 decomp_ctr[4];
      decomp_ctr[0] = BigVecQ3{BigRat::Times(norm_ctr[0].x, scale0),
                               BigRat::Times(norm_ctr[0].y, scale0),
                               BigRat::Times(norm_ctr[0].z, scale0)};
      for (int j = 1; j < 4; j++) decomp_ctr[j] = norm_ctr[j];

      BigRat oct_r = BigRat::Times(BigRat(7, 4), BigRat::Plus(c, delta));
      BigVecQ3 targets[6] = {
        {oct_r, BigRat(0), BigRat(0)},
        {-oct_r, BigRat(0), BigRat(0)},
        {BigRat(0), oct_r, BigRat(0)},
        {BigRat(0), -oct_r, BigRat(0)},
        {BigRat(0), BigRat(0), oct_r},
        {BigRat(0), BigRat(0), -oct_r}
      };

      double min_overall = 1e9;
      for (int k = 0; k < 6; k++) {
        vec3 p0 = {decomp_ctr[0].x.ToDouble(), decomp_ctr[0].y.ToDouble(), decomp_ctr[0].z.ToDouble()};
        vec3 p1 = {decomp_ctr[1].x.ToDouble(), decomp_ctr[1].y.ToDouble(), decomp_ctr[1].z.ToDouble()};
        vec3 p2 = {decomp_ctr[2].x.ToDouble(), decomp_ctr[2].y.ToDouble(), decomp_ctr[2].z.ToDouble()};
        vec3 p3 = {decomp_ctr[3].x.ToDouble(), decomp_ctr[3].y.ToDouble(), decomp_ctr[3].z.ToDouble()};
        vec3 tgt = {targets[k].x.ToDouble(), targets[k].y.ToDouble(), targets[k].z.ToDouble()};

        // Barycentric coords:
        // Solve [p0-p3, p1-p3, p2-p3] * [l0, l1, l2] = tgt - p3
        vec3 a = p0 - p3;
        vec3 b = p1 - p3;
        vec3 d = p2 - p3;
        vec3 y = tgt - p3;
        double D = yocto::dot(a, yocto::cross(b, d));
        double l0 = yocto::dot(y, yocto::cross(b, d)) / D;
        double l1 = yocto::dot(a, yocto::cross(y, d)) / D;
        double l2 = yocto::dot(a, yocto::cross(b, y)) / D;
        double l3 = 1.0 - l0 - l1 - l2;
        min_overall = std::min({min_overall, l0, l1, l2, l3});
      }
      std::cout << "c = " << c_val << ", c_cone = " << c_cone_val << " -> min_l = " << min_overall << "\n";
    }
  }

  return 0;
}
