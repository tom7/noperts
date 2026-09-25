#include <iostream>
#include <vector>
#include <algorithm>
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
  std::string target = "03121303200";
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

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 3000);

  std::vector<vec3> u_list;
  std::vector<int> orig_idx;
  for (size_t i = 0; i < base_axes.size(); i++) {
    const auto &ba = base_axes[i];
    vec3 v = {ba.center.x.ToDouble() / ba.cert.B.ToDouble(),
              ba.center.y.ToDouble() / ba.cert.B.ToDouble(),
              ba.center.z.ToDouble() / ba.cert.B.ToDouble()};
    if (yocto::dot(v, u0) < 0) {
      u_list.push_back(v);
      orig_idx.push_back(i);
    }
  }
  std::cout << "Filtered to " << u_list.size() << " opposing axes\n";

  double delta = 0.000234013;

  for (double c_cone : {0.0385, 0.039, 0.0395, 0.040}) {
    for (double box_c : {0.0001, 0.0002, 0.0005, 0.001, 0.002, 0.005, 0.010, 0.020}) {
      double scale = (box_c + delta) / c_cone;
      vec3 v0 = u0 * scale;
      double R = 1.75 * (box_c + delta);

      std::vector<vec3> oct = {
        {R, 0, 0}, {-R, 0, 0},
        {0, R, 0}, {0, -R, 0},
        {0, 0, R}, {0, 0, -R}
      };

      // Select top 120 most diverse opposing axes
      // Diversity: greedy farthest point sampling
      int K = std::min(120, (int)u_list.size());
      std::vector<int> sample;
      sample.push_back(0);
      std::vector<double> min_dist(u_list.size(), 1e9);

      for (int step = 1; step < K; step++) {
        int last = sample.back();
        int best_next = -1;
        double max_d = -1;
        for (size_t i = 0; i < u_list.size(); i++) {
          double d = yocto::length(u_list[i] - u_list[last]);
          if (d < min_dist[i]) min_dist[i] = d;
          if (min_dist[i] > max_d) {
            max_d = min_dist[i];
            best_next = i;
          }
        }
        sample.push_back(best_next);
      }

      double best_min_l = -1.0;
      int bi = -1, bj = -1, bk = -1;

      for (int i = 0; i < K; i++) {
        vec3 d1 = u_list[sample[i]] - v0;
        for (int j = i + 1; j < K; j++) {
          vec3 d2 = u_list[sample[j]] - v0;
          vec3 c12 = yocto::cross(d1, d2);
          if (yocto::length(c12) < 1e-6) continue;

          for (int k = j + 1; k < K; k++) {
            vec3 d3 = u_list[sample[k]] - v0;
            double det = yocto::dot(c12, d3);
            if (std::abs(det) < 1e-8) continue;

            vec3 c23 = yocto::cross(d2, d3);
            vec3 c31 = yocto::cross(d3, d1);

            double min_l = 1e9;
            for (const auto &p : oct) {
              vec3 dp = p - v0;
              double l1 = yocto::dot(dp, c23) / det;
              double l2 = yocto::dot(dp, c31) / det;
              double l3 = yocto::dot(dp, c12) / det;
              double l0 = 1.0 - l1 - l2 - l3;
              double m = std::min({l0, l1, l2, l3});
              if (m < min_l) min_l = m;
              if (min_l <= best_min_l) break;
            }

            if (min_l > best_min_l) {
              best_min_l = min_l;
              bi = orig_idx[sample[i]];
              bj = orig_idx[sample[j]];
              bk = orig_idx[sample[k]];
            }
          }
        }
      }

      if (best_min_l > 0) {
        std::cout << "SUCCESS! c_cone = " << c_cone << ", box_c = " << box_c
                  << ": best_min_l = " << best_min_l << " with axes (" << bi << ", " << bj << ", " << bk << ")\n";
        return 0;
      }
    }
  }

  std::cout << "No positive cage found with sampled axes.\n";
  return 0;
}
