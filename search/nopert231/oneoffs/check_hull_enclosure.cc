#include <iostream>
#include <vector>
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

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static bool InTetrahedron(const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3, const vec3 &p, double margin = 0.0) {
  vec3 d0 = v0 - v3;
  vec3 d1 = v1 - v3;
  vec3 d2 = v2 - v3;
  double d = Det3(d0, d1, d2);
  if (fabs(d) < 1e-12) return false;

  vec3 dp = p - v3;
  double b0 = Det3(dp, d1, d2) / d;
  double b1 = Det3(d0, dp, d2) / d;
  double b2 = Det3(d0, d1, dp) / d;
  double b3 = 1.0 - b0 - b1 - b2;

  return (b0 >= margin && b1 >= margin && b2 >= margin && b3 >= margin);
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

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

  vec3 u0 = {ctr_ann.x.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.y.ToDouble() / ax_ann.B.ToDouble(),
             ctr_ann.z.ToDouble() / ax_ann.B.ToDouble()};

  double c_cone = 0.0133;
  double c = 0.0018;
  double delta = 0.0013;
  double scale = (c + delta) / c_cone;
  vec3 v0 = scale * u0;

  double R_target = 1.75 * (c + delta);
  vec3 targets[6] = {
    {+R_target, 0, 0},
    {-R_target, 0, 0},
    {0, +R_target, 0},
    {0, -R_target, 0},
    {0, 0, +R_target},
    {0, 0, -R_target}
  };

  std::vector<vec3> centers(base_axes.size());
  for (size_t i = 0; i < base_axes.size(); i++) {
    centers[i] = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
                  base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
                  base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
  }

  // Pre-filter candidate complement axes:
  // We need axes that have negative z (since v0 has small negative z)
  // We need axes with positive x, negative x, positive y, negative y
  std::vector<size_t> neg_z, pos_x, neg_x, pos_y, neg_y;
  for (size_t i = 0; i < centers.size(); i++) {
    if (base_axes[i].delta.ToDouble() > delta) continue;
    if (centers[i].z < -0.005) neg_z.push_back(i);
    if (centers[i].x > 0.1) pos_x.push_back(i);
    if (centers[i].x < -0.1) neg_x.push_back(i);
    if (centers[i].y > 0.05) pos_y.push_back(i);
    if (centers[i].y < -0.05) neg_y.push_back(i);
  }

  std::cout << "Filtered: neg_z=" << neg_z.size()
            << ", pos_x=" << pos_x.size()
            << ", neg_x=" << neg_x.size()
            << ", pos_y=" << pos_y.size()
            << ", neg_y=" << neg_y.size() << "\n";

  // Check structured combinations: pick i1 from neg_z, i2 from pos_x, i3 from neg_x ...
  int checks = 0;
  for (size_t i1 : neg_z) {
    for (size_t i2 : pos_x) {
      for (size_t i3 : neg_x) {
        checks++;
        const vec3 &v1 = centers[i1];
        const vec3 &v2 = centers[i2];
        const vec3 &v3 = centers[i3];

        bool all_in = true;
        for (int k = 0; k < 6; k++) {
          if (!InTetrahedron(v0, v1, v2, v3, targets[k], 1e-6)) {
            all_in = false;
            break;
          }
        }
        if (all_in) {
          std::cout << "FOUND WINNING CAGE! i1=" << i1 << ", i2=" << i2 << ", i3=" << i3 << "\n";
          std::cout << "v1=" << v1.x << "," << v1.y << "," << v1.z << "\n";
          std::cout << "v2=" << v2.x << "," << v2.y << "," << v2.z << "\n";
          std::cout << "v3=" << v3.x << "," << v3.y << "," << v3.z << "\n";
          return 0;
        }
      }
    }
  }

  std::cout << "Tested " << checks << " structured triples. None enclosed all 6.\n";
  return 0;
}
