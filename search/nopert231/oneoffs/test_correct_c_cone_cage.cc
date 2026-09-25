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

static inline bool InTetrahedron(const vec3 &v0, const vec3 &v1, const vec3 &v2, const vec3 &v3, const vec3 &p, double margin = 1e-6) {
  vec3 d0 = v0 - v3;
  vec3 d1 = v1 - v3;
  vec3 d2 = v2 - v3;
  double d = Det3(d0, d1, d2);
  if (fabs(d) < 1e-12) return false;

  vec3 dp = p - v3;
  double b0 = Det3(dp, d1, d2) / d;
  if (b0 < margin) return false;
  double b1 = Det3(d0, dp, d2) / d;
  if (b1 < margin) return false;
  double b2 = Det3(d0, d1, dp) / d;
  if (b2 < margin) return false;
  double b3 = 1.0 - b0 - b1 - b2;
  return (b3 >= margin);
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

  // With ||u0|| = 0.003977:
  // We need ||v0|| = ((c + delta)/c_cone) * ||u0|| >= 1.75 * (c + delta)
  // => c_cone <= ||u0|| / 1.75 = 0.00227
  // Let c_cone = 20 / 10000 = 0.0020
  // delta = 115 / 100000 = 0.00115 (since del_ann = 0.001121)
  // Let c = 14 / 10000 = 0.0014 (so c - delta = 0.00025 >= r/2)
  BigRat c_cone("20/10000");   // 0.0020
  BigRat delta("115/100000");  // 0.00115
  BigRat c("140/100000");      // 0.00140

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

  std::cout << "||v0|| = " << yocto::length(v0_f) << ", R_target = " << R_f << "\n";
  std::cout << "Ratio ||v0|| / R_target = " << yocto::length(v0_f) / R_f << " (MUST BE > 1!)\n";

  std::vector<size_t> cand_indices;
  std::vector<vec3> cand_centers_f;
  for (size_t i = 0; i < base_axes.size(); i++) {
    if (base_axes[i].delta <= delta) {
      cand_indices.push_back(i);
      cand_centers_f.push_back({base_axes[i].center.x.ToDouble(),
                                base_axes[i].center.y.ToDouble(),
                                base_axes[i].center.z.ToDouble()});
    }
  }

  std::cout << "Candidates with delta <= " << delta.ToDouble() << ": " << cand_indices.size() << " axes\n";

  std::mt19937 rng(42);
  std::uniform_int_distribution<size_t> dist(0, cand_indices.size() - 1);

  for (int iter = 0; iter < 10000000; iter++) {
    size_t i1 = dist(rng), i2 = dist(rng), i3 = dist(rng);
    if (i1 == i2 || i2 == i3 || i1 == i3) continue;

    const vec3 &v1 = cand_centers_f[i1];
    const vec3 &v2 = cand_centers_f[i2];
    const vec3 &v3 = cand_centers_f[i3];

    bool in_double = true;
    for (int k = 0; k < 6; k++) {
      if (!InTetrahedron(v0_f, v1, v2, v3, targets_f[k], 1e-6)) {
        in_double = false; break;
      }
    }
    if (in_double) {
      std::cout << "SUCCESS! Found winning cage at iter " << iter << "!\n";
      std::cout << "Indices: " << cand_indices[i1] << ", " << cand_indices[i2] << ", " << cand_indices[i3] << "\n";
      return 0;
    }
  }

  std::cout << "Not found in 10M iterations.\n";
  return 1;
}
