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

  // v_core:
  ContactInfo core_contacts[3] = {
    MakeContact(3, 2, 2, 1, 0, 2),
    MakeContact(1, 4, 4, 8, 0, 4),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate core_cert;
  BigVecQ3 core_center;
  BigRat core_delta;
  std::string err;
  Tube229::AuditAxis(tri, core_contacts, &core_cert, &core_center, &core_delta, &err, BigRat(0));
  BigVecQ3 v_core_norm = core_center / core_cert.B;

  // Comp 0, 1, 2 from test_6axis_cage.cc:
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);

  // Re-run the greedy selection from test_6axis_cage.cc:
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));
  vec3 u0 = {center0.x.ToDouble() / ax0.B.ToDouble(),
             center0.y.ToDouble() / ax0.B.ToDouble(),
             center0.z.ToDouble() / ax0.B.ToDouble()};

  std::vector<vec3> pool;
  for (const auto &ax : axes500) {
    vec3 c = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    if (yocto::length(c) > 1e-12) pool.push_back(c);
  }

  int N = 50000;
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

  // Test tetrahedron: {v_core, Comp 0, Comp 1, Comp 2}
  std::vector<BigVecQ3> tet = {v_core_norm};
  for (int k = 0; k < 3; k++) {
    const auto &ax = axes500[selected[k]];
    tet.push_back(ax.center / ax.cert.B);
  }

  BigRat inrad = Tube229::ExactTetrahedronAxisRadius(tet.data());
  std::cout << "Inradius of {v_core, Comp 0, Comp 1, Comp 2}: " << inrad.ToDouble() << "\n";

  // Check if ALL 4 axes have ZERO defect:
  std::cout << "v_core defect: zero\n";
  for (int k = 0; k < 3; k++) {
    std::cout << "Comp " << k << " delta=" << axes500[selected[k]].delta.ToDouble() << "\n";
  }

  return 0;
}
