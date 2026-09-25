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

  // Comp 0, 1, 2 from test_6axis_cage.cc:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);

  // The 3 complement axes from test_6axis_cage.cc:
  int comp_idx[3] = {0, 1, 2}; // we will find the exact 3 from test_6axis_cage
  std::vector<vec3> pool;
  for (const auto &ax : axes500) {
    vec3 c = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    pool.push_back(c);
  }

  int N = 200000;
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

  // Load v_core:
  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_cert, &core_center, &core_delta, &err, BigRat(0));
  vec3 v_core = {core_center.x.ToDouble() / core_cert.B.ToDouble(),
                 core_center.y.ToDouble() / core_cert.B.ToDouble(),
                 core_center.z.ToDouble() / core_cert.B.ToDouble()};

  for (int num_comps : {5, 8, 12, 16, 20, 25, 30}) {
    std::vector<int> selected;
    std::vector<double> max_dots(pts.size(), -1e9);

    while ((int)selected.size() < num_comps) {

      double worst_dot = 1e9;
      int worst_pt = -1;
      for (size_t i = 0; i < pts.size(); i++) {
        if (max_dots[i] < worst_dot) {
          worst_dot = max_dots[i];
          worst_pt = i;
        }
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
      if (best_cand == -1) break;
      selected.push_back(best_cand);
      for (size_t i = 0; i < pts.size(); i++) {
        double d = yocto::dot(pts[i], pool[best_cand]);
        if (d > max_dots[i]) max_dots[i] = d;
      }
    }

    // Test across entire sphere:
    double box_c = 0.005;
    double min_dot0 = 1e9;
    double min_core = 1e9;
    int fail_count = 0;

    int N_all = 500000;
    for (int i = 0; i < N_all; i++) {
      double z = 1.0 - (2.0 * i + 1.0) / N_all;
      double r = std::sqrt(std::max(0.0, 1.0 - z * z));
      double phi = i * 2.399963229728653;
      vec3 a = {r * std::cos(phi), r * std::sin(phi), z};

      double max_comp = -1e9;
      for (int s : selected) {
        double d = yocto::dot(a, pool[s]);
        if (d > max_comp) max_comp = d;
      }
      if (max_comp < box_c) {
        fail_count++;
        double d0 = yocto::dot(a, u0);
        if (d0 < min_dot0) min_dot0 = d0;
        double d_core = yocto::dot(a, v_core);
        if (d_core < min_core) min_core = d_core;
      }
    }
    std::cout << "Comps: " << num_comps << " -> fail points: " << fail_count
              << " / " << N_all << ", Min dot(a, u0): " << min_dot0
              << ", Min dot(a, v_core): " << min_core << "\n";
    if (min_core < 0) {
      for (int i = 0; i < N_all; i++) {
        double z = 1.0 - (2.0 * i + 1.0) / N_all;
        double r = std::sqrt(std::max(0.0, 1.0 - z * z));
        double phi = i * 2.399963229728653;
        vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
        double max_comp = -1e9;
        for (int s : selected) {
          double d = yocto::dot(a, pool[s]);
          if (d > max_comp) max_comp = d;
        }
        if (max_comp < box_c && yocto::dot(a, v_core) < -0.003) {
          std::cout << "Found worst fail point: a = (" << a.x << ", " << a.y << ", " << a.z
                    << "), dot0 = " << yocto::dot(a, u0)
                    << ", dot_core = " << yocto::dot(a, v_core) << "\n";
          break;
        }
      }
    }
  }

  return 0;
}


