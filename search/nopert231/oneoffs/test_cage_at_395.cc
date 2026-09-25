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

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  std::cout << "Loaded " << base_axes.size() << " axes\n";

  std::vector<vec3> u_list;
  for (const auto &ba : base_axes) {
    u_list.push_back({ba.center.x.ToDouble() / ba.cert.B.ToDouble(),
                      ba.center.y.ToDouble() / ba.cert.B.ToDouble(),
                      ba.center.z.ToDouble() / ba.cert.B.ToDouble()});
  }

  double delta = 0.000234013;
  double c_cone = 0.0395;

  for (double box_c : {0.0001, 0.0002, 0.0003, 0.0005}) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);

    std::vector<vec3> oct = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };

    std::vector<int> candidates;
    for (size_t i = 0; i < u_list.size(); i++) {
      if (yocto::dot(u_list[i], u0) < 0) {
        candidates.push_back(i);
      }
    }

    int C = candidates.size();
    double best_min_l = -1.0;
    int best_i = -1, best_j = -1, best_k = -1;

    for (int i = 0; i < C; i++) {
      vec3 d1 = u_list[candidates[i]] - v0;
      for (int j = i + 1; j < C; j++) {
        vec3 d2 = u_list[candidates[j]] - v0;
        vec3 c12 = yocto::cross(d1, d2);
        if (yocto::length(c12) < 1e-6) continue;

        for (int k = j + 1; k < C; k++) {
          vec3 d3 = u_list[candidates[k]] - v0;
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
            best_i = candidates[i];
            best_j = candidates[j];
            best_k = candidates[k];
          }
        }
      }
    }
    std::cout << "box_c = " << box_c << ": best_min_l = " << best_min_l
              << " with axes (" << best_i << ", " << best_j << ", " << best_k << ")\n";
    if (best_min_l >= 0) break;
  }

  return 0;
}
