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

  // Annular axes:
  ContactInfo cts[4][3] = {
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14) },
    { MakeContact(3, 2, 2, 1, 600, 2), MakeContact(1, 4, 4, 8, 600, 4), MakeContact(13, 14, 14, 15, 800, 14) },
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 400, 4), MakeContact(13, 14, 14, 15, 800, 14) },
    { MakeContact(3, 2, 2, 1, 600, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 600, 14) }
  };

  BigVecQ3 ctr[4]; BigRat B[4]; BigRat del[4]; std::string err;
  for (int j = 0; j < 4; j++) {
    AxisCertificate ax;
    Tube229::AuditAxis(tri, cts[j], &ax, &ctr[j], &del[j], &err, j == 0 ? BigRat(5, 1000) : BigRat(0));
    B[j] = ax.B;
  }

  vec3 norm_ctr[4];
  for (int j = 0; j < 4; j++) {
    norm_ctr[j] = vec3{ctr[j].x.ToDouble() / B[j].ToDouble(),
                       ctr[j].y.ToDouble() / B[j].ToDouble(),
                       ctr[j].z.ToDouble() / B[j].ToDouble()};
  }

  double delta = del[0].ToDouble();
  double c_val = 0.00018;
  double c_cone_val = 0.0286;

  double scale0 = (c_val + delta) / c_cone_val;
  vec3 p[4];
  p[0] = norm_ctr[0] * scale0;
  for (int j = 1; j < 4; j++) p[j] = norm_ctr[j];

  double oct_r = 1.75 * (c_val + delta);
  vec3 targets[6] = {
    {oct_r, 0, 0}, {-oct_r, 0, 0},
    {0, oct_r, 0}, {0, -oct_r, 0},
    {0, 0, oct_r}, {0, 0, -oct_r}
  };

  for (int k = 0; k < 6; k++) {
    vec3 tgt = targets[k];
    double V0 = yocto::dot(p[1] - tgt, yocto::cross(p[2] - tgt, p[3] - tgt));
    double V1 = yocto::dot(tgt - p[0], yocto::cross(p[2] - p[0], p[3] - p[0]));
    double V2 = yocto::dot(p[1] - p[0], yocto::cross(tgt - p[0], p[3] - p[0]));
    double V3 = yocto::dot(p[1] - p[0], yocto::cross(p[2] - p[0], tgt - p[0]));
    double V = yocto::dot(p[1] - p[0], yocto::cross(p[2] - p[0], p[3] - p[0]));
    std::cout << "Target " << k << ": V = " << V << ", l0=" << V0/V << ", l1=" << V1/V << ", l2=" << V2/V << ", l3=" << V3/V << "\n";
  }

  return 0;
}
