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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  struct Cand {
    int idx;
    vec3 u;
  };
  std::vector<Cand> c1_zpos, c2_yneg_xpos, c3_yneg_xneg;

  for (size_t i = 0; i < base_axes.size(); i++) {
    const auto &ax = base_axes[i];
    vec3 u = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    if (u.z > 0.02) c1_zpos.push_back({(int)i, u});
    if (u.y < -0.005 && u.x > 0) c2_yneg_xpos.push_back({(int)i, u});
    if (u.y < -0.005 && u.x < 0) c3_yneg_xneg.push_back({(int)i, u});
  }

  std::cout << "c1 (+z): " << c1_zpos.size() << "\n";
  std::cout << "c2 (-y, +x): " << c2_yneg_xpos.size() << "\n";
  std::cout << "c3 (-y, -x): " << c3_yneg_xneg.size() << "\n";

  // Sort each cluster to take the best 40
  std::sort(c1_zpos.begin(), c1_zpos.end(), [](const Cand &a, const Cand &b) {
    return a.u.z > b.u.z;
  });
  std::sort(c2_yneg_xpos.begin(), c2_yneg_xpos.end(), [](const Cand &a, const Cand &b) {
    return (a.u.x - a.u.y) > (b.u.x - b.u.y);
  });
  std::sort(c3_yneg_xneg.begin(), c3_yneg_xneg.end(), [](const Cand &a, const Cand &b) {
    return (-a.u.x - a.u.y) > (-b.u.x - b.u.y);
  });

  if (c1_zpos.size() > 40) c1_zpos.resize(40);
  if (c2_yneg_xpos.size() > 40) c2_yneg_xpos.resize(40);
  if (c3_yneg_xneg.size() > 40) c3_yneg_xneg.resize(40);

  double delta = 0.000234013;
  double box_c = 0.001;

  for (double c_cone : {0.040, 0.038, 0.035, 0.032, 0.030}) {
    double scale = (box_c + delta) / c_cone;
    vec3 v0 = u0 * scale;
    double R = 1.75 * (box_c + delta);

    std::vector<vec3> oct = {
      {R, 0, 0}, {-R, 0, 0},
      {0, R, 0}, {0, -R, 0},
      {0, 0, R}, {0, 0, -R}
    };

    double best_min_l = -1.0;
    int bi = -1, bj = -1, bk = -1;

    for (const auto &cand1 : c1_zpos) {
      vec3 v1 = cand1.u;
      for (const auto &cand2 : c2_yneg_xpos) {
        vec3 v2 = cand2.u;
        for (const auto &cand3 : c3_yneg_xneg) {
          vec3 v3 = cand3.u;

          vec3 d1 = v1 - v0, d2 = v2 - v0, d3 = v3 - v0;
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
            if (min_l <= 0) break;
          }

          if (min_l > best_min_l) {
            best_min_l = min_l;
            bi = cand1.idx; bj = cand2.idx; bk = cand3.idx;
          }
        }
      }
    }
    std::cout << "c_cone = " << c_cone << ": best_min_l = " << best_min_l;
    if (best_min_l > 0) {
      std::cout << " (SUCCESS! indices " << bi << ", " << bj << ", " << bk << ")";
    }
    std::cout << "\n";
  }

  return 0;
}
