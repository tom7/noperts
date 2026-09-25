#include <iostream>
#include <iomanip>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  int m[12] = {
    150, 1000, 882,
    50, 800, 950,
    1000, 1000, 343,
    113, 320, 150
  };

  ContactInfo c[4][3] = {
    { MakeContact(3, 2, 2, 1, m[0], 2),
      MakeContact(1, 4, 4, 8, m[1], 4),
      MakeContact(13, 14, 14, 15, m[2], 14) },
    { MakeContact(2, 1, 1, 4, m[3], 1),
      MakeContact(10, 15, 15, 19, m[4], 15),
      MakeContact(19, 3, 3, 2, m[5], 3) },
    { MakeContact(2, 1, 1, 4, m[6], 1),
      MakeContact(8, 9, 9, 10, m[7], 9),
      MakeContact(9, 10, 10, 15, m[8], 10) },
    { MakeContact(3, 2, 2, 1, m[9], 2),
      MakeContact(1, 4, 4, 8, m[10], 4),
      MakeContact(10, 15, 15, 19, m[11], 15) }
  };

  std::string err;
  AxisCertificate ax[4];
  BigVecQ3 cnt[4];
  BigRat var_radius[4];

  for (int a = 0; a < 4; a++) {
    if (!Tube229::AuditAxis(tri, c[a], &ax[a], &cnt[a], &var_radius[a], &err, BigRat(5, 1000))) {
      std::cerr << "Audit failed for axis " << a << "\n";
      return 1;
    }
  }

  BigRat delta(234013, 1000000000);
  BigRat variationError(1, 1000000000);
  BigRat c_cone(278, 10000);
  BigRat box_c(255, 1000000);
  BigRat box_r(1, 2000); // 0.0005

  std::cout << "--- 1. B_pos ---\n";
  for (int a = 0; a < 4; a++) {
    std::cout << "  ax[" << a << "].B > 0: " << (ax[a].B > 0) << "\n";
  }

  std::cout << "--- 2. var (variation bound) ---\n";
  for (int a = 0; a < 4; a++) {
    BigRat lhs = var_radius[a] + BigRat(3) * variationError;
    BigRat rhs = ax[a].B * delta;
    std::cout << "  ax[" << a << "] var: lhs <= rhs? " << (lhs <= rhs)
              << " (" << lhs.ToDouble() << " <= " << rhs.ToDouble() << ")\n";
  }

  std::cout << "--- 3. delta_lt_ccone ---\n";
  std::cout << "  delta < c_cone: " << (delta < c_cone) << "\n";

  std::cout << "--- 4. c_cone_lt_one ---\n";
  std::cout << "  c_cone < 1: " << (c_cone < 1) << "\n";

  std::cout << "--- 5. comp_angle: dot(u0, c0) >= c_cone ---\n";
  // u0 = cnt[0] / B[0], c0 = cnt[0] / B[0] (here coreAxis is axis 0 itself!)
  // Since coreAxis IS axis 0, dot(u0, coreAxis) = dot(u0, u0) = 1 >= c_cone!
  // Wait, in Lean:
  // dot(box.certificate 0, box.coreAxis) >= c_cone * B_0 * B_core
  BigRat dot00 = cnt[0].x * cnt[0].x + cnt[0].y * cnt[0].y + cnt[0].z * cnt[0].z;
  BigRat norm0 = ax[0].B; // wait, B is norm of cross product?
  // In Lean:
  // certificate j has direction cnt[j].
  // certificate j .B is B.
  // And the condition is:
  // c_cone * (box.certificate 0).B * box.coreAxis.B <= dot(box.certificate 0, box.coreAxis)
  BigRat comp_lhs = c_cone * ax[0].B * ax[0].B;
  BigRat comp_rhs = dot00;
  std::cout << "  comp_angle: lhs <= rhs? " << (comp_lhs <= comp_rhs)
            << " (" << comp_lhs.ToDouble() << " <= " << comp_rhs.ToDouble() << ")\n";

  std::cout << "--- 6. Support defect D0 ---\n";
  // Ax0 is a pure support axis audited by AuditAxis.
  BigRat def0(0);
  std::cout << "  Defect D0 = " << def0.ToString() << " (" << def0.ToDouble() << ")\n";

  std::cout << "--- 7. Annular dominance ---\n";
  // With D0 = 0: (1/4) * r^4 <= r_min^2 * (c_cone - delta)^2
  // Let's compute r_min:
  // r_min = min { box_c - delta, 1 - r - (box_c + delta) }
  BigRat r_min1 = box_c - delta;
  BigRat r_min2 = BigRat(1) - box_r - (box_c + delta);
  BigRat r_min = (r_min1 < r_min2 ? r_min1 : r_min2);
  std::cout << "  r_min = " << r_min.ToDouble() << "\n";
  BigRat ann_lhs = BigRat(1, 4) * box_r * box_r * box_r * box_r;
  BigRat ann_rhs = r_min * r_min * (c_cone - delta) * (c_cone - delta);
  std::cout << "  annular dominance: lhs <= rhs? " << (ann_lhs <= ann_rhs)
            << " (" << ann_lhs.ToDouble() << " <= " << ann_rhs.ToDouble() << ")\n";

  std::cout << "--- 8. Cage Barycentric Coordinates on 6 Octahedron Vertices ---\n";
  // v0 = ((box_c + delta) / c_cone) * (cnt[0] / B[0])
  // v1 = cnt[1] / B[1], v2 = cnt[2] / B[2], v3 = cnt[3] / B[3]
  // In Lean:
  // cageApex = ((box.c + box.δ) / box.c_cone) • (box.certificate 0).direction
  // (notice Lean divides certificate j by B_j in the simplex formula or directly uses cageApex)
  // Let's check the exact formula in AtlasProjectiveAnnularCertificate.lean:
  // cage apex v0: ((box.c + box.δ) / box.c_cone) • ( (certificate 0).direction / B0 )
  // cage vertex j (for j=1,2,3): (certificate j).direction / Bj
  vec3 u_dbl[4];
  for (int a = 0; a < 4; a++) {
    u_dbl[a] = {cnt[a].x.ToDouble() / ax[a].B.ToDouble(),
                cnt[a].y.ToDouble() / ax[a].B.ToDouble(),
                cnt[a].z.ToDouble() / ax[a].B.ToDouble()};
  }
  vec3 v0_dbl = u_dbl[0] * ((box_c.ToDouble() + delta.ToDouble()) / c_cone.ToDouble());
  vec3 v1_dbl = u_dbl[1];
  vec3 v2_dbl = u_dbl[2];
  vec3 v3_dbl = u_dbl[3];

  double R = 1.75 * (box_c.ToDouble() + delta.ToDouble());
  vec3 oct[6] = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  vec3 d1 = v1_dbl - v0_dbl;
  vec3 d2 = v2_dbl - v0_dbl;
  vec3 d3 = v3_dbl - v0_dbl;
  vec3 c12 = yocto::cross(d1, d2);
  double det = yocto::dot(c12, d3);
  vec3 c23 = yocto::cross(d2, d3);
  vec3 c31 = yocto::cross(d3, d1);

  double min_l = 1.0;
  for (int p = 0; p < 6; p++) {
    vec3 dp = oct[p] - v0_dbl;
    double l1 = yocto::dot(dp, c23) / det;
    double l2 = yocto::dot(dp, c31) / det;
    double l3 = yocto::dot(dp, c12) / det;
    double l0 = 1.0 - l1 - l2 - l3;
    std::cout << "  oct[" << p << "]: l0=" << l0 << " l1=" << l1 << " l2=" << l2 << " l3=" << l3 << "\n";
    min_l = std::min({min_l, l0, l1, l2, l3});
  }
  std::cout << "  min_l across all 6 octahedron vertices = " << min_l << "\n";

  std::cout << "--- 9. Hineq (c + delta < (1 - r) * (1 - c_cone)) ---\n";
  BigRat h_lhs = box_c + delta;
  BigRat h_rhs = (BigRat(1) - box_r) * (BigRat(1) - c_cone);
  std::cout << "  hineq: lhs < rhs? " << (h_lhs < h_rhs)
            << " (" << h_lhs.ToDouble() << " < " << h_rhs.ToDouble() << ")\n";

  return 0;
}
