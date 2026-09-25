#include <iostream>
#include <vector>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(),
             ctr0.y.ToDouble() / ax0.B.ToDouble(),
             ctr0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Loaded " << base_axes.size() << " hull support axes\n";

  vec3 axis = yocto::normalize(-u0);
  vec3 perp1 = yocto::normalize(yocto::cross(axis, vec3{1, 0, 0}));
  if (yocto::length(yocto::cross(axis, vec3{1, 0, 0})) < 0.1) {
    perp1 = yocto::normalize(yocto::cross(axis, vec3{0, 1, 0}));
  }
  vec3 perp2 = yocto::cross(axis, perp1);

  double rad = 84.0 * M_PI / 180.0;
  double ca = std::cos(rad);
  double sa = std::sin(rad);

  vec3 ideal1 = yocto::normalize(axis * ca + perp1 * sa);
  vec3 ideal2 = yocto::normalize(axis * ca + (perp1 * (-0.5) + perp2 * (std::sqrt(3.0)/2.0)) * sa);
  vec3 ideal3 = yocto::normalize(axis * ca + (perp1 * (-0.5) - perp2 * (std::sqrt(3.0)/2.0)) * sa);

  // Find top 20 closest axes to each ideal direction:
  auto find_closest = [&](const vec3 &target_dir) {
    std::vector<std::pair<double, int>> ranked;
    for (size_t i = 0; i < base_axes.size(); i++) {
      vec3 u = {base_axes[i].center.x.ToDouble() / base_axes[i].cert.B.ToDouble(),
                base_axes[i].center.y.ToDouble() / base_axes[i].cert.B.ToDouble(),
                base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble()};
      double d = yocto::dot(yocto::normalize(u), target_dir);
      ranked.push_back({d, (int)i});
    }
    std::sort(ranked.rbegin(), ranked.rend());
    std::vector<int> res;
    for (int k = 0; k < std::min((int)ranked.size(), 30); k++) {
      res.push_back(ranked[k].second);
    }
    std::cout << "Target dot with closest: " << ranked[0].first << "\n";
    return res;
  };

  auto c1 = find_closest(ideal1);
  auto c2 = find_closest(ideal2);
  auto c3 = find_closest(ideal3);

  double delta = 3.33e-7;
  double c_cone = 0.028;
  double box_c = 1e-7;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);

  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  double best_min_l = -1;
  int bi = -1, bj = -1, bk = -1;

  for (int idx1 : c1) {
    vec3 u1 = {base_axes[idx1].center.x.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
               base_axes[idx1].center.y.ToDouble() / base_axes[idx1].cert.B.ToDouble(),
               base_axes[idx1].center.z.ToDouble() / base_axes[idx1].cert.B.ToDouble()};
    vec3 d1 = u1 - v0;
    for (int idx2 : c2) {
      vec3 u2 = {base_axes[idx2].center.x.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
                 base_axes[idx2].center.y.ToDouble() / base_axes[idx2].cert.B.ToDouble(),
                 base_axes[idx2].center.z.ToDouble() / base_axes[idx2].cert.B.ToDouble()};
      vec3 d2 = u2 - v0;
      for (int idx3 : c3) {
        vec3 u3 = {base_axes[idx3].center.x.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
                   base_axes[idx3].center.y.ToDouble() / base_axes[idx3].cert.B.ToDouble(),
                   base_axes[idx3].center.z.ToDouble() / base_axes[idx3].cert.B.ToDouble()};
        vec3 d3 = u3 - v0;

        double det = yocto::dot(d1, yocto::cross(d2, d3));
        if (std::abs(det) < 1e-8) continue;
        vec3 c23 = yocto::cross(d2, d3);
        vec3 c31 = yocto::cross(d3, d1);
        vec3 c12 = yocto::cross(d1, d2);

        double min_l = 1e9;
        for (const auto &p : oct) {
          vec3 dp = p - v0;
          double l1 = yocto::dot(dp, c23) / det;
          double l2 = yocto::dot(dp, c31) / det;
          double l3 = yocto::dot(dp, c12) / det;
          double l0 = 1.0 - l1 - l2 - l3;
          min_l = std::min({min_l, l0, l1, l2, l3});
        }
        if (min_l > best_min_l) {
          best_min_l = min_l;
          bi = idx1; bj = idx2; bk = idx3;
          std::cout << "Candidate triple (" << bi << ", " << bj << ", " << bk
                    << "): min_l = " << best_min_l << "\n";
        }
      }
    }
  }

  std::cout << "Best min_l: " << best_min_l << "\n";
  return 0;
}
