#include <iostream>
#include <vector>
#include <cmath>
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

  std::vector<std::pair<int, vec3>> full_pool;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= 0.000200) {
      double B = axes[i].cert.B.ToDouble();
      vec3 v = vec3{axes[i].center.x.ToDouble() / B, axes[i].center.y.ToDouble() / B, axes[i].center.z.ToDouble() / B};
      full_pool.push_back({(int)i, v});
    }
  }

  int ci = 50;
  ContactInfo c0[3] = { {3, 2, 2, 1, 800, 2}, {1, 4, 4, 8, 800, 4}, contacts[ci] };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0));
  vec3 u0 = vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};

  double c_cone = 0.010;
  double c_box = 0.001;
  double delta = 0.000180;
  double R = 1.75 * (c_box + delta);
  vec3 targets[6] = {
    {+R, 0, 0}, {-R, 0, 0},
    {0, +R, 0}, {0, -R, 0},
    {0, 0, +R}, {0, 0, -R}
  };

  vec3 v0 = ((c_box + delta) / c_cone) * u0;

  // Ref axes: 34, 4074, 7968
  vec3 r1, r2, r3;
  for (const auto &item : full_pool) {
    if (item.first == 34) r1 = item.second;
    if (item.first == 4074) r2 = item.second;
    if (item.first == 7968) r3 = item.second;
  }

  std::vector<std::pair<int, vec3>> n1, n2, n3;
  for (const auto &item : full_pool) {
    if (yocto::length(item.second - r1) < 0.06) n1.push_back(item);
    if (yocto::length(item.second - r2) < 0.06) n2.push_back(item);
    if (yocto::length(item.second - r3) < 0.06) n3.push_back(item);
  }

  std::cout << "Neighborhood sizes: " << n1.size() << ", " << n2.size() << ", " << n3.size() << "\n";

  double best_min_b = -1e9;
  int bi = -1, bj = -1, bk = -1;

  for (const auto &p1 : n1) {
    vec3 v1 = p1.second;
    for (const auto &p2 : n2) {
      vec3 v2 = p2.second;
      for (const auto &p3 : n3) {
        vec3 v3 = p3.second;

        vec3 d0 = v0 - v3;
        vec3 d1 = v1 - v3;
        vec3 d2 = v2 - v3;
        double det = Det3(d0, d1, d2);
        if (std::abs(det) < 1e-7) continue;

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
          bi = p1.first; bj = p2.first; bk = p3.first;
          if (min_b > 1e-4) {
            std::cout << "FOUND STRICTLY POSITIVE CAGE! min_b = " << min_b
                      << " with axes (" << bi << ", " << bj << ", " << bk << ")\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Best refined min_b: " << best_min_b << "\n";
  return 0;
}
