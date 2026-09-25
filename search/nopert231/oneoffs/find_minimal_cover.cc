#include <iostream>
#include <vector>
#include <cmath>
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
  vec3 u = {center0.x.ToDouble(), center0.y.ToDouble(), center0.z.ToDouble()};

  // Build candidate pool of zero-defect axes:
  std::vector<vec3> pool;
  std::vector<Tube229::AuditedAxis> audited_pool;

  // Add all 500 hull support axes:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  for (const auto &cand : axes500) {
    audited_pool.push_back(cand);
    pool.push_back({cand.center.x.ToDouble(), cand.center.y.ToDouble(), cand.center.z.ToDouble()});
  }

  // Also add varied contact axes:
  ContactInfo comp[3][3] = {
    {{15, 19, 19, 3, 200, 19}, {2, 1, 1, 4, 200, 1}, {8, 9, 9, 10, 200, 9}},
    {{2, 1, 1, 4, 0, 1}, {10, 15, 15, 19, 333, 15}, {10, 15, 15, 19, 0, 15}},
    {{3, 2, 2, 1, 800, 2}, {4, 8, 8, 9, 800, 8}, {14, 15, 15, 19, 800, 15}}
  };
  for (int i = 0; i < 3; i++) {
    AxisCertificate ax; BigVecQ3 ctr; BigRat del;
    if (Tube229::AuditAxis(tri, comp[i], &ax, &ctr, &del, &err, BigRat(0))) {
      audited_pool.push_back({ax, ctr, del});
      pool.push_back({ctr.x.ToDouble(), ctr.y.ToDouble(), ctr.z.ToDouble()});
    }
  }

  int N = 50000;
  for (double c_cone : {0.032, 0.033, 0.034, 0.035}) {
    std::cout << "\n================ c_cone = " << c_cone << " ================\n";
    std::vector<vec3> pts;
    for (int i = 0; i < N; i++) {
      double z = 1.0 - (2.0 * i + 1.0) / N;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi = i * 2.399963229728653;
      vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
      vec3 u0_norm = u / ax0.B.ToDouble();
      if (yocto::dot(a, u0_norm) < c_cone) {
        pts.push_back(a);
      }
    }



    std::vector<int> selected;
    double min_margin = 0.0001;
    std::vector<double> max_dots(pts.size(), -1e9);

    while (selected.size() < 10) {
      double worst_dot = 1e9;
      int worst_pt = -1;
      for (size_t i = 0; i < pts.size(); i++) {
        if (max_dots[i] < worst_dot) {
          worst_dot = max_dots[i];
          worst_pt = i;
        }
      }
      if (worst_dot >= min_margin) {
        std::cout << "Covered with " << selected.size() << " axes! Min margin: " << worst_dot << "\n";
        break;
      }
      int best_cand = -1;
      double best_min = -1e9;
      for (size_t c = 0; c < pool.size(); c++) {
        double d = yocto::dot(pts[worst_pt], pool[c]);
        if (d > best_min) {
          best_min = d;
          best_cand = c;
        }
      }
      if (best_cand == -1 || best_min <= 0) {
        std::cout << "Failed to find cand, best_min=" << best_min << ", worst_dot=" << worst_dot << "\n";
        break;
      }

      selected.push_back(best_cand);
      for (size_t i = 0; i < pts.size(); i++) {
        double d = yocto::dot(pts[i], pool[best_cand]);
        if (d > max_dots[i]) max_dots[i] = d;
      }
    }
  }
  return 0;
}

