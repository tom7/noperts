#include <iostream>
#include <iomanip>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static double Det4(double m[4][4]) {
  double d = 0;
  for (int c = 0; c < 4; c++) {
    double sub[3][3];
    for (int r = 0; r < 3; r++) {
      int sc = 0;
      for (int j = 0; j < 4; j++) {
        if (j == c) continue;
        sub[r][sc++] = m[r][j];
      }
    }
    double d3 = sub[0][0] * (sub[1][1] * sub[2][2] - sub[1][2] * sub[2][1])
              - sub[0][1] * (sub[1][0] * sub[2][2] - sub[1][2] * sub[2][0])
              + sub[0][2] * (sub[1][0] * sub[2][1] - sub[1][1] * sub[2][0]);
    double term = m[3][c] * d3;
    if ((3 + c) % 2 == 1) d -= term;
    else d += term;
  }
  return d;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  double box_delta = 234013.0 / 1000000000.0;
  double box_c = 1.0 / 1000.0;

  // Ax0
  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  // Ax1
  ContactInfo c1[3] = {
    {2, 10, 10, 2, 0, 10},
    {1, 15, 15, 1, 333, 15},
    {4, 19, 19, 4, 333, 19}
  };
  // Ax2
  ContactInfo c2[3] = {
    {2, 10, 10, 3, 0, 10},
    {1, 15, 15, 2, 666, 15},
    {4, 19, 19, 1, 0, 19}
  };
  // Ax3
  ContactInfo c3[3] = {
    {2, 1, 1, 15, 0, 1},
    {1, 4, 4, 19, 333, 4},
    {4, 8, 8, 3, 1000, 8}
  };

  AxisCertificate ax[4];
  BigVecQ3 ctr[4];
  BigRat del[4];
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax[0], &ctr[0], &del[0], &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c1, &ax[1], &ctr[1], &del[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax[2], &ctr[2], &del[2], &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax[3], &ctr[3], &del[3], &err, BigRat(0));

  vec3 v[4];
  for (int j = 0; j < 4; j++) {
    v[j] = {ctr[j].x.ToDouble() / ax[j].B.ToDouble(),
            ctr[j].y.ToDouble() / ax[j].B.ToDouble(),
            ctr[j].z.ToDouble() / ax[j].B.ToDouble()};
  }

  double oct_rad = (7.0 / 4.0) * (box_c + box_delta);
  vec3 oct[6] = {
    {oct_rad, 0, 0}, {-oct_rad, 0, 0},
    {0, oct_rad, 0}, {0, -oct_rad, 0},
    {0, 0, oct_rad}, {0, 0, -oct_rad}
  };

  std::cout << "Testing c_cone range for oct_rad = " << oct_rad << ":\n";
  for (int c_cone_int = 1; c_cone_int <= 35; c_cone_int++) {
    double c_cone = c_cone_int / 1000.0;
    double scale = (box_c + box_delta) / c_cone;
    vec3 cv0 = v[0] * scale;

    double M[4][4] = {
      {cv0.x, v[1].x, v[2].x, v[3].x},
      {cv0.y, v[1].y, v[2].y, v[3].y},
      {cv0.z, v[1].z, v[2].z, v[3].z},
      {1.0,   1.0,    1.0,    1.0}
    };
    double detM = Det4(M);
    if (std::abs(detM) < 1e-12) continue;

    bool all_pos = true;
    for (int k = 0; k < 6; k++) {
      double tgt[4] = {oct[k].x, oct[k].y, oct[k].z, 1.0};
      for (int j = 0; j < 4; j++) {
        double M_sub[4][4];
        for (int r = 0; r < 4; r++) {
          for (int c = 0; c < 4; c++) {
            M_sub[r][c] = (c == j) ? tgt[r] : M[r][c];
          }
        }
        double b_j = Det4(M_sub) / detM;
        if (b_j < -1e-9) {
          all_pos = false;
          break;
        }
      }
      if (!all_pos) break;
    }
    if (all_pos) {
      std::cout << "c_cone = " << c_cone << " is VALID!\n";
    }
  }

  return 0;
}
