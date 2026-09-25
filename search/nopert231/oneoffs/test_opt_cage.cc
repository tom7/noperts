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

  double box_c = 0.0001;
  double c_cone = 0.015;
  double scale0 = (box_c + del0.ToDouble()) / (c_cone * ax0.B.ToDouble());
  vec3 v0 = {ctr0.x.ToDouble() * scale0, ctr0.y.ToDouble() * scale0, ctr0.z.ToDouble() * scale0};
  std::cout << "v0 = (" << v0.x << ", " << v0.y << ", " << v0.z << "), |v0| = " << yocto::length(v0) << "\n";

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Loaded " << axes.size() << " axes.\n";

  std::vector<vec3> u;
  for (const auto &ax : axes) {
    u.push_back(vec3{ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                     ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                     ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  int N = u.size();
  double best_min_l = -1;
  int b1 = -1, b2 = -1, b3 = -1;

  // We want the tetrahedron (v0, u[i], u[j], u[k]) to enclose the octahedron of radius 1.75 * (box_c + delta)
  double delta = del0.ToDouble();
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  for (int i = 0; i < N; i++) {
    vec3 v1 = u[i];
    for (int j = i + 1; j < N; j++) {
      vec3 v2 = u[j];
      for (int k = j + 1; k < N; k++) {
        vec3 v3 = u[k];

        vec3 d1 = v1 - v0;
        vec3 d2 = v2 - v0;
        vec3 d3 = v3 - v0;
        double det = yocto::dot(d1, yocto::cross(d2, d3));
        if (std::abs(det) < 1e-8) continue;

        vec3 c23 = yocto::cross(d2, d3);
        double min_l = 1e9;

        for (const auto &p : oct) {
          vec3 dp = p - v0;
          double l1 = yocto::dot(dp, c23) / det;
          double l2 = yocto::dot(d1, yocto::cross(dp, d3)) / det;
          double l3 = yocto::dot(d1, yocto::cross(d2, dp)) / det;
          double l0 = 1.0 - l1 - l2 - l3;
          min_l = std::min({min_l, l0, l1, l2, l3});
        }

        if (min_l > best_min_l) {
          best_min_l = min_l;
          b1 = i; b2 = j; b3 = k;
    if (best_min_l > 0) {
      std::cout << "FOUND VALID CAGE: (" << b1 << ", " << b2 << ", " << b3 << "), min_l = " << best_min_l << "\n";
      for (int idx : {b1, b2, b3}) {
        std::cout << "Axis " << idx << ": B=" << axes[idx].cert.B.ToString()
                  << ", del=" << axes[idx].delta.ToString() << "\n";
        for (int i = 0; i < 3; i++) {
          const auto &ci = axes[idx].cert.contacts[i];
          std::cout << "  contact " << i << ": v=" << ci.vertex << " e1=(" << ci.edge_start << "," << ci.edge_finish << ") e2=(" << ci.edge_start2 << "," << ci.edge_finish2 << ") mix=" << ci.mix << "\n";
        }
      }
      return 0;
    }
        }
      }
    }
  }

  std::cout << "Best min_l = " << best_min_l << " with (" << b1 << ", " << b2 << ", " << b3 << ")\n";
  return 0;
}
