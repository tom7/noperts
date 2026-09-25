#include <iostream>
#include <vector>
#include <random>
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

static inline double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

static inline int NumEnclosed(const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3, const vec3 targets[6]) {
  vec3 d0 = v0 - v3;
  vec3 d1 = v1 - v3;
  vec3 d2 = v2 - v3;
  double d = Det3(d0, d1, d2);
  if (fabs(d) < 1e-12) return 0;

  int count = 0;
  for (int k = 0; k < 6; k++) {
    vec3 dp = targets[k] - v3;
    double b0 = Det3(dp, d1, d2) / d;
    double b1 = Det3(d0, dp, d2) / d;
    double b2 = Det3(d0, d1, dp) / d;
    double b3 = 1.0 - b0 - b1 - b2;
    if (b0 >= -1e-7 && b1 >= -1e-7 && b2 >= -1e-7 && b3 >= -1e-7) {
      count++;
    }
  }
  return count;
}

int main() {
  std::string target_path = "03121300";
  TriangleQ tri = TriangleFromPath(target_path);
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

  BigRat c_cone("133/10000"); // 0.0133
  BigRat delta("13/10000");   // 0.0013
  BigRat c("18/10000");       // 0.0018

  BigRat v0_scale = (c + delta) / c_cone;
  BigVecQ3 v0 = ctr_ann * v0_scale;
  vec3 v0_f = {v0.x.ToDouble(), v0.y.ToDouble(), v0.z.ToDouble()};

  BigRat target_scale = (c + delta) * BigRat(7, 4);
  double R_f = target_scale.ToDouble();
  vec3 targets_f[6] = {
    {+R_f, 0, 0}, {-R_f, 0, 0},
    {0, +R_f, 0}, {0, -R_f, 0},
    {0, 0, +R_f}, {0, 0, -R_f}
  };

  std::vector<vec3> cand_centers_f;
  for (size_t i = 0; i < base_axes.size(); i++) {
    cand_centers_f.push_back({base_axes[i].center.x.ToDouble(),
                              base_axes[i].center.y.ToDouble(),
                              base_axes[i].center.z.ToDouble()});
  }

  std::mt19937 rng(42);
  std::uniform_int_distribution<size_t> dist(0, cand_centers_f.size() - 1);

  int max_count = 0;
  for (int iter = 0; iter < 1000000; iter++) {
    size_t i1 = dist(rng), i2 = dist(rng), i3 = dist(rng);
    if (i1 == i2 || i2 == i3 || i1 == i3) continue;
    int c_enc = NumEnclosed(v0_f, cand_centers_f[i1], cand_centers_f[i2], cand_centers_f[i3], targets_f);
    if (c_enc > max_count) {
      max_count = c_enc;
      std::cout << "iter " << iter << ": max enclosed = " << max_count << "/6\n";
    }
  }

  return 0;
}
