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
  BigVecQ3 u0 = center0 / ax0.B;

  // Let's take the 5 complement axes from find_minimal_cover:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<BigVecQ3> pool_centers;
  for (const auto &ax : axes500) {
    pool_centers.push_back(ax.center / ax.cert.B);
  }

  // Find greedy set of complement axes that maximize the inradius with u0:
  // For a set of vertices V = {u0, v1, v2, ..., vk}:
  // The inradius around 0 is min_{||a||=1} max_{v in V} dot(a, v).
  // Let's compute this over 100,000 points on S^2:
  int N = 100000;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts.push_back({(float)(r * std::cos(phi)), (float)(r * std::sin(phi)), (float)z});
  }

  vec3 u0_v = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};
  std::vector<vec3> pool_v;
  for (const auto &c : pool_centers) {
    pool_v.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
  }

  std::vector<int> selected;
  std::vector<double> max_dots(N);
  for (int i = 0; i < N; i++) {
    max_dots[i] = yocto::dot(pts[i], u0_v);
  }

  for (int iter = 0; iter < 10; iter++) {
    double min_dot = 1e9;
    int worst_pt = -1;
    for (int i = 0; i < N; i++) {
      if (max_dots[i] < min_dot) {
        min_dot = max_dots[i];
        worst_pt = i;
      }
    }
    std::cout << "Cage with " << (1 + selected.size()) << " axes: inradius = " << min_dot << "\n";
    if (min_dot >= 0.035) {
      std::cout << "SUCCESS! Inradius reached " << min_dot << " >= 0.035!\n";
      break;
    }

    int best_cand = -1;
    double best_val = -1e9;
    for (size_t c = 0; c < pool_v.size(); c++) {
      double d = yocto::dot(pts[worst_pt], pool_v[c]);
      if (d > best_val) {
        best_val = d;
        best_cand = c;
      }
    }
    if (best_cand == -1) break;
    selected.push_back(best_cand);
    for (int i = 0; i < N; i++) {
      double d = yocto::dot(pts[i], pool_v[best_cand]);
      if (d > max_dots[i]) max_dots[i] = d;
    }
  }

  return 0;
}
