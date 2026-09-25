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

  // Generate dense candidate contacts:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 200, 400, 600, 800, 1000}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    cand_contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  std::vector<AxisCertificate> dense_certs;
  std::vector<vec3> u;

  // Also include 500 axes from FindAllHullSupportAxes:
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 500);
  for (const auto &ax : base_axes) {
    dense_certs.push_back(ax.cert);
    u.push_back({ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
                 ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
                 ax.center.z.ToDouble() / ax.cert.B.ToDouble()});
  }

  int C = cand_contacts.size();
  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          if (delta == BigRat(0)) {
            dense_certs.push_back(ax);
            u.push_back({center.x.ToDouble() / ax.B.ToDouble(),
                         center.y.ToDouble() / ax.B.ToDouble(),
                         center.z.ToDouble() / ax.B.ToDouble()});
          }
        }
      }
    }
  }

  std::cout << "Total candidate axes: " << u.size() << "\n";

  double delta = 0.000234013;
  double c_cone = 0.028;
  double box_c = 0.0005;
  double scale = (box_c + delta) / c_cone;
  vec3 v0 = u0 * scale;
  double R = 1.75 * (box_c + delta);
  std::vector<vec3> oct = {
    {R, 0, 0}, {-R, 0, 0},
    {0, R, 0}, {0, -R, 0},
    {0, 0, R}, {0, 0, -R}
  };

  int N = u.size();
  double best_min_l = -1;
  int best_i = -1, best_j = -1, best_k = -1;

  for (int i = 0; i < N; i++) {
    vec3 v1 = u[i];
    for (int j = i + 1; j < N; j++) {
      vec3 v2 = u[j];
      for (int k = j + 1; k < N; k++) {
        vec3 v3 = u[k];

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
        }

        if (min_l > best_min_l) {
          best_min_l = min_l;
          best_i = i; best_j = j; best_k = k;
          if (best_min_l > 0) {
            std::cout << "SUCCESS! Found cage with min_l = " << best_min_l
                      << " using axes " << i << ", " << j << ", " << k << "\n";
            return 0;
          }
        }
      }
    }
  }

  std::cout << "Best min_l: " << best_min_l << "\n";
  return 0;
}
