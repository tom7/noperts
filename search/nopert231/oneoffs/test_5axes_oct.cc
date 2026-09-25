#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  double box_c = 0.0008;
  double c_cone = 0.024;
  double delta = del0.ToDouble();
  double scale0 = box_c / (c_cone * ax0.B.ToDouble());
  vec3 v0 = {ctr0.x.ToDouble() * scale0, ctr0.y.ToDouble() * scale0, ctr0.z.ToDouble() * scale0};

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  int chosen[4] = {0, 24, 210, 424};
  std::vector<vec3> u;
  u.push_back(v0);
  for (int idx : chosen) {
    u.push_back(vec3{axes[idx].center.x.ToDouble() / axes[idx].cert.B.ToDouble(),
                     axes[idx].center.y.ToDouble() / axes[idx].cert.B.ToDouble(),
                     axes[idx].center.z.ToDouble() / axes[idx].cert.B.ToDouble()});
  }

  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  std::cout << "R = " << R << ", |v0| = " << yocto::length(v0) << "\n";

  // Check if each oct point is in convex hull of u[0..4]:
  // Since convex hull of 5 points is union of tetrahedra formed by 4 points:
  for (int k = 0; k < 6; k++) {
    vec3 p = oct[k];
    bool in_hull = false;
    for (int omit = 0; omit < 5 && !in_hull; omit++) {
      std::vector<vec3> tet;
      for (int i = 0; i < 5; i++) if (i != omit) tet.push_back(u[i]);
      vec3 d1 = tet[1] - tet[0];
      vec3 d2 = tet[2] - tet[0];
      vec3 d3 = tet[3] - tet[0];
      double det = yocto::dot(d1, yocto::cross(d2, d3));
      if (std::abs(det) < 1e-9) continue;
      vec3 dp = p - tet[0];
      double l1 = yocto::dot(dp, yocto::cross(d2, d3)) / det;
      double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
      double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
      double l0 = 1.0 - l1 - l2 - l3;
      if (l0 >= -1e-6 && l1 >= -1e-6 && l2 >= -1e-6 && l3 >= -1e-6) {
        in_hull = true;
      }
    }
    std::cout << "Oct point " << k << " in hull: " << (in_hull ? "YES" : "NO") << "\n";
  }

  return 0;
}
