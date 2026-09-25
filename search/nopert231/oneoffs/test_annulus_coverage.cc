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
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  // Comp 0, 1, 2:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<vec3> pool;
  for (const auto &ax : axes500) {
    vec3 c = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    if (yocto::length(c) > 1e-12) pool.push_back(c);
  }

  // The 4 selected complement axes from test_6axis_cage.cc:
  int N = 100000;
  double c_cone = 0.035;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    if (yocto::dot(a, u0) < c_cone) pts.push_back(a);
  }

  std::vector<int> selected;
  double min_margin = 0.0001;
  std::vector<double> max_dots(pts.size(), -1e9);

  while (selected.size() < 4) {
    double worst_dot = 1e9;
    int worst_pt = -1;
    for (size_t i = 0; i < pts.size(); i++) {
      if (max_dots[i] < worst_dot) {
        worst_dot = max_dots[i];
        worst_pt = i;
      }
    }
    if (worst_dot >= min_margin) break;
    int best_cand = -1;
    double best_min = -1e9;
    for (size_t c = 0; c < pool.size(); c++) {
      double d = yocto::dot(pts[worst_pt], pool[c]);
      if (d > best_min) {
        best_min = d;
        best_cand = c;
      }
    }
    if (best_cand == -1 || best_min <= 0) break;
    selected.push_back(best_cand);
    for (size_t i = 0; i < pts.size(); i++) {
      double d = yocto::dot(pts[i], pool[best_cand]);
      if (d > max_dots[i]) max_dots[i] = d;
    }
  }

  // Let's test points in the annulus: box.c <= dot(a, u0) < c_cone_high
  double box_c = 0.005;
  double c_cone_high = 0.045;

  std::cout << "Testing points in annulus [" << box_c << ", " << c_cone_high << "):\n";
  int annulus_pts = 0;
  double min_comp_margin_in_annulus = 1e9;
  double min_comp4_margin_in_annulus = 1e9;

  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    double dot0 = yocto::dot(a, u0);
    if (dot0 >= box_c && dot0 < c_cone_high) {
      annulus_pts++;
      // Check max dot with comp 0, 1, 2:
      double m3 = -1e9;
      for (int k = 0; k < 3; k++) {
        double d = yocto::dot(a, pool[selected[k]]);
        if (d > m3) m3 = d;
      }
      if (m3 < min_comp_margin_in_annulus) min_comp_margin_in_annulus = m3;

      // Check max dot with all 4 comps:
      double m4 = m3;
      if (selected.size() >= 4) {
        double d = yocto::dot(a, pool[selected[3]]);
        if (d > m4) m4 = d;
      }
      if (m4 < min_comp4_margin_in_annulus) min_comp4_margin_in_annulus = m4;
    }
  }

  std::cout << "Found " << annulus_pts << " points in annulus.\n";
  std::cout << "Min margin with 3 comps in annulus: " << min_comp_margin_in_annulus << "\n";
  std::cout << "Min margin with 4 comps in annulus: " << min_comp4_margin_in_annulus << "\n";

  return 0;
}
