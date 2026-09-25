#include <iostream>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static inline double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_ann[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_ann;
  BigVecQ3 ctr_ann;
  BigRat del_ann;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ax_ann, &ctr_ann, &del_ann, &err, BigRat(0));

  ContactInfo c_comp[3][3] = {
    { MakeContact(15, 19, 19, 3, 200, 19), MakeContact(2, 1, 1, 4, 200, 1), MakeContact(8, 9, 9, 10, 200, 9) },
    { MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 333, 15), MakeContact(10, 15, 15, 19, 0, 15) },
    { MakeContact(3, 2, 2, 1, 800, 2), MakeContact(4, 8, 8, 9, 800, 8), MakeContact(14, 15, 15, 19, 800, 15) }
  };

  BigVecQ3 comp_centers[3];
  AxisCertificate comp_axes[3];
  BigRat comp_deltas[3];
  for (int a = 0; a < 3; a++) {
    Tube229::AuditAxis(tri, c_comp[a], &comp_axes[a], &comp_centers[a], &comp_deltas[a], &err, BigRat(0));
  }

  // Let's test scaled v0
  // v0 = ((c + delta)/c_cone) * ctr_ann / B
  // or pure centers
  vec3 p0 = {ctr_ann.x.ToDouble(), ctr_ann.y.ToDouble(), ctr_ann.z.ToDouble()};
  vec3 p1 = {comp_centers[0].x.ToDouble(), comp_centers[0].y.ToDouble(), comp_centers[0].z.ToDouble()};
  vec3 p2 = {comp_centers[1].x.ToDouble(), comp_centers[1].y.ToDouble(), comp_centers[1].z.ToDouble()};
  vec3 p3 = {comp_centers[2].x.ToDouble(), comp_centers[2].y.ToDouble(), comp_centers[2].z.ToDouble()};

  vec3 d0 = p0 - p3;
  vec3 d1 = p1 - p3;
  vec3 d2 = p2 - p3;
  double d = Det3(d0, d1, d2);
  std::cout << "Det3 = " << d << "\n";

  vec3 dp = -p3; // target is origin
  double b0 = Det3(dp, d1, d2) / d;
  double b1 = Det3(d0, dp, d2) / d;
  double b2 = Det3(d0, d1, dp) / d;
  double b3 = 1.0 - b0 - b1 - b2;
  std::cout << "Origin barycentric coords: b0=" << b0 << ", b1=" << b1 << ", b2=" << b2 << ", b3=" << b3 << "\n";

  return 0;
}
