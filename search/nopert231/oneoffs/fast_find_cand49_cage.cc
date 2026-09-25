#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

static double Det3(const vec3 &a, const vec3 &b, const vec3 &c) {
  return yocto::dot(a, yocto::cross(b, c));
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 50000);

  vec3 tri_f[3] = { ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2]) };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;
  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});

  // Candidate 49 as ax0:
  ContactInfo c0[3] = { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, contacts[49] };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0));

  double c_cone = 0.017;
  double c_box = 0.001;
  double delta = 0.000196;
  vec3 u0 = vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 v0 = ((c_box + delta) / c_cone) * u0;

  double R = 1.75 * (c_box + delta);
  vec3 targets[6] = {
    {+R, 0, 0}, {-R, 0, 0},
    {0, +R, 0}, {0, -R, 0},
    {0, 0, +R}, {0, 0, -R}
  };

  // Original v1, v2, v3
  ContactInfo c1[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 500, 15}, {3, 2, 2, 1, 0, 2} };
  ContactInfo c2[3] = { {2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 666, 15}, {3, 2, 2, 1, 0, 2} };
  ContactInfo c3[3] = { {2, 1, 1, 4, 0, 1}, {1, 4, 4, 8, 333, 4}, {15, 19, 19, 3, 1000, 19} };
  AxisCertificate orig_ax[4]; BigVecQ3 orig_ctr[4]; BigRat orig_del[4];
  Tube229::AuditAxis(tri, c1, &orig_ax[1], &orig_ctr[1], &orig_del[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &orig_ax[2], &orig_ctr[2], &orig_del[2], &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &orig_ax[3], &orig_ctr[3], &orig_del[3], &err, BigRat(0));

  vec3 ref_v[4];
  for (int j = 1; j < 4; j++) {
    ref_v[j] = vec3{orig_ctr[j].x.ToDouble() / orig_ax[j].B.ToDouble(),
                    orig_ctr[j].y.ToDouble() / orig_ax[j].B.ToDouble(),
                    orig_ctr[j].z.ToDouble() / orig_ax[j].B.ToDouble()};
  }

  // Filter pool with delta <= 0.000200
  std::vector<std::pair<int, vec3>> pool1, pool2, pool3;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000200) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      double d1 = yocto::length(v - ref_v[1]);
      double d2 = yocto::length(v - ref_v[2]);
      double d3 = yocto::length(v - ref_v[3]);
      if (d1 < 0.04) pool1.push_back({(int)i, v});
      if (d2 < 0.04) pool2.push_back({(int)i, v});
      if (d3 < 0.04) pool3.push_back({(int)i, v});
    }
  }

  std::cout << "Pool sizes: " << pool1.size() << ", " << pool2.size() << ", " << pool3.size() << "\n";

  double best_min_b = -1e9;
  int best_i = -1, best_j = -1, best_k = -1;

  for (const auto &p1 : pool1) {
    vec3 v1 = p1.second;
    for (const auto &p2 : pool2) {
      vec3 v2 = p2.second;
      for (const auto &p3 : pool3) {
        vec3 v3 = p3.second;

        vec3 d0 = v0 - v3;
        vec3 d1 = v1 - v3;
        vec3 d2 = v2 - v3;
        double det = Det3(d0, d1, d2);
        if (std::abs(det) < 1e-8) continue;

        double min_b = 1e9;
        for (int t = 0; t < 6; t++) {
          vec3 dp = targets[t] - v3;
          double b0 = Det3(dp, d1, d2) / det;
          double b1 = Det3(d0, dp, d2) / det;
          double b2 = Det3(d0, d1, dp) / det;
          double b3 = 1.0 - b0 - b1 - b2;
          min_b = std::min({min_b, b0, b1, b2, b3});
        }
        if (min_b > best_min_b) {
          best_min_b = min_b;
          best_i = p1.first; best_j = p2.first; best_k = p3.first;
        }
      }
    }
  }

  std::cout << "Best min_b: " << best_min_b << " with axes (" << best_i << ", " << best_j << ", " << best_k << ")\n";
  return 0;
}
