#include <iostream>
#include <vector>
#include <random>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static vec3 ToDouble(const BigVecQ3 &v) { return {v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()}; }

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

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Hull support pool size: " << base_axes.size() << "\n";

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
  // Let c be small enough, e.g. 0.0001 or 0.0005, delta = 0.0013
  // Notice: c can be chosen as long as comp_angle holds:
  // r^2 * (1 + (c - delta)^2) <= 4 * (c - delta)^2
  // For r = 1/2000 = 0.0005: (c - delta) >= r / 2 = 0.00025.
  // So c >= delta + 0.00025 = 0.0013 + 0.00025 = 0.00155.
  // Setting c = 0.0018 satisfies comp_angle!
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

  std::cout << "v0 = (" << v0.x << ", " << v0.y << ", " << v0.z << "), ||v0|| = " << yocto::length(v0) << "\n";
  std::cout << "R_target = " << R_target << "\n";

  std::vector<vec3> centers(base_axes.size());
  for (size_t i = 0; i < base_axes.size(); i++) {
    centers[i] = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
                  base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
                  base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
  }

  std::cout << "Searching for winning 3-axis complement cage enclosing octahedron...\n";

  std::mt19937 rng(42);
  std::uniform_int_distribution<size_t> dist(0, base_axes.size() - 1);

  for (int iter = 0; iter < 10000000; iter++) {
    size_t i1 = dist(rng);
    size_t i2 = dist(rng);
    size_t i3 = dist(rng);
    if (i1 == i2 || i2 == i3 || i1 == i3) continue;

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
      std::cout << "FOUND WINNING CAGE! indices: " << i1 << ", " << i2 << ", " << i3 << "\n";
      std::cout << "iter = " << iter << "\n";
      std::cout << "Axis " << i1 << ": B=" << base_axes[i1].cert.B.ToDouble() << ", delta=" << base_axes[i1].delta.ToDouble() << "\n";
      std::cout << "Axis " << i2 << ": B=" << base_axes[i2].cert.B.ToDouble() << ", delta=" << base_axes[i2].delta.ToDouble() << "\n";
      std::cout << "Axis " << i3 << ": B=" << base_axes[i3].cert.B.ToDouble() << ", delta=" << base_axes[i3].delta.ToDouble() << "\n";
      return 0;
    }
  }

  std::cout << "Not found in 10M iterations.\n";
  return 1;
}
