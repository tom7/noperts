#include <iostream>
#include <vector>
#include <iomanip>
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

  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 644, 15),
    MakeContact(3, 2, 2, 1, 0, 2)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 236, 1),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 200, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 540, 2),
    MakeContact(8, 9, 9, 10, 200, 9),
    MakeContact(3, 2, 2, 1, 541, 2)
  };

  std::string err;
  AxisCertificate ax1, ax2, ax3;
  BigVecQ3 cnt1, cnt2, cnt3;
  BigRat dlt1, dlt2, dlt3;
  Tube229::AuditAxis(tri, c1, &ax1, &cnt1, &dlt1, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c2, &ax2, &cnt2, &dlt2, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c3, &ax3, &cnt3, &dlt3, &err, BigRat(5, 1000));

  vec3 v1 = {cnt1.x.ToDouble() / ax1.B.ToDouble(), cnt1.y.ToDouble() / ax1.B.ToDouble(), cnt1.z.ToDouble() / ax1.B.ToDouble()};
  vec3 v2 = {cnt2.x.ToDouble() / ax2.B.ToDouble(), cnt2.y.ToDouble() / ax2.B.ToDouble(), cnt2.z.ToDouble() / ax2.B.ToDouble()};
  vec3 v3 = {cnt3.x.ToDouble() / ax3.B.ToDouble(), cnt3.y.ToDouble() / ax3.B.ToDouble(), cnt3.z.ToDouble() / ax3.B.ToDouble()};

  double delta = 0.000234013;
  double box_c = 0.000255;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  // Base c0 mix: (800, 800, 200)
  // Sweep dm0, dm1, dm2 around (800, 800, 200) and c_cone around 0.0278
  double best_min_l = -1e9;
  int best_dm[3] = {0, 0, 0};
  double best_cc = 0;

  for (double c_cone = 0.0265; c_cone <= 0.0285; c_cone += 0.0002) {
    for (int dm0 = -20; dm0 <= 20; dm0 += 5) {
      for (int dm1 = -20; dm1 <= 20; dm1 += 5) {
        for (int dm2 = -20; dm2 <= 20; dm2 += 5) {
          ContactInfo c0[3] = {
            MakeContact(3, 2, 2, 1, 800 + dm0, 2),
            MakeContact(1, 4, 4, 8, 800 + dm1, 4),
            MakeContact(13, 14, 14, 15, 200 + dm2, 14)
          };
          AxisCertificate ax0;
          BigVecQ3 cnt0;
          BigRat dlt0;
          if (!Tube229::AuditAxis(tri, c0, &ax0, &cnt0, &dlt0, &err, BigRat(5, 1000))) continue;
          vec3 u0 = {cnt0.x.ToDouble() / ax0.B.ToDouble(), cnt0.y.ToDouble() / ax0.B.ToDouble(), cnt0.z.ToDouble() / ax0.B.ToDouble()};
          vec3 v0 = u0 * ((box_c + delta) / c_cone);

          vec3 d1 = v1 - v0;
          vec3 d2 = v2 - v0;
          vec3 d3 = v3 - v0;
          vec3 c12 = yocto::cross(d1, d2);
          vec3 c23 = yocto::cross(d2, d3);
          vec3 c31 = yocto::cross(d3, d1);
          double det = yocto::dot(c12, d3);
          if (std::abs(det) < 1e-12) continue;

          double min_l = 1.0;
          for (int p = 0; p < 6; p++) {
            vec3 dp = oct[p] - v0;
            double l1 = yocto::dot(dp, c23) / det;
            double l2 = yocto::dot(dp, c31) / det;
            double l3 = yocto::dot(dp, c12) / det;
            double l0 = 1.0 - l1 - l2 - l3;
            min_l = std::min({min_l, l0, l1, l2, l3});
          }

          if (min_l > best_min_l) {
            best_min_l = min_l;
            best_dm[0] = dm0; best_dm[1] = dm1; best_dm[2] = dm2;
            best_cc = c_cone;
            std::cout << "c_cone=" << c_cone << " dm=(" << dm0 << "," << dm1 << "," << dm2
                      << ") -> min_l = " << min_l << "\n";
            if (min_l > 0) {
              std::cout << "POSITIVE OCTAHEDRON CAGE ACHIEVED!\n";
              return 0;
            }
          }
        }
      }
    }
  }

  std::cout << "Finished sweep. Best min_l = " << best_min_l << "\n";
  return 0;
}
