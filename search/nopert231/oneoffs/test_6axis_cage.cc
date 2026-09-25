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

  // Get 500 hull support axes and find the 5 minimal covering axes for c_cone = 0.035
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<vec3> pool;
  for (const auto &ax : axes500) {
    vec3 c = {ax.center.x.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.y.ToDouble() / ax.cert.B.ToDouble(),
              ax.center.z.ToDouble() / ax.cert.B.ToDouble()};
    if (yocto::length(c) > 1e-12) {
      pool.push_back(c);
    }
  }

  int N = 50000;
  double c_cone = 0.035;
  std::vector<vec3> pts;
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    vec3 a = {r * std::cos(phi), r * std::sin(phi), z};
    if (yocto::dot(a, u0) < c_cone) {
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

  // Tetrahedron skipping comp 3: uses comp 0, 1, 2!
  std::cout << "\n================ 4-AXIS TETRAHEDRON (Axis 0 + comp 0, 1, 2) ================\n";
  int c_indices[3] = {selected[0], selected[1], selected[2]};
  std::vector<AxisCertificate> tet_axes = {ax0};
  std::vector<BigVecQ3> tet_centers = {center0 / ax0.B};
  for (int i = 0; i < 3; i++) {
    const auto &ax = axes500[c_indices[i]];
    tet_axes.push_back(ax.cert);
    tet_centers.push_back(ax.center / ax.cert.B);
    std::cout << "Comp " << i << ": contacts=("
              << ax.cert.contacts[0].vertex << ", "
              << ax.cert.contacts[1].vertex << ", "
              << ax.cert.contacts[2].vertex << ") mixes=("
              << ax.cert.contacts[0].mix << ", "
              << ax.cert.contacts[1].mix << ", "
              << ax.cert.contacts[2].mix << ") B="
              << ax.cert.B.ToDouble() << " delta="
              << ax.delta.ToDouble() << "\n";
  }

  BigRat exact_inrad = Tube229::ExactTetrahedronAxisRadius(tet_centers.data());
  std::cout << "EXACT RATIONAL INRADIUS: " << exact_inrad.ToDouble() << "\n";

  // Test barycentric with exact rational arithmetic:
  for (double c_cand : {0.005, 0.004, 0.003, 0.002, 0.001}) {
    BigRat c = BigRat::FromDouble(c_cand);
    BigRat delta(3, 10000); // 0.0003
    bool bary_ok = true;
    for (int k = 0; k < 6; k++) {
      BigVecQ3 target = BigVecQ3{BigRat(0), BigRat(0), BigRat(0)};
      BigRat scale = BigRat(7, 4) * (c + delta);
      if (k == 0) target.x = scale;
      else if (k == 1) target.x = -scale;
      else if (k == 2) target.y = scale;
      else if (k == 3) target.y = -scale;
      else if (k == 4) target.z = scale;
      else if (k == 5) target.z = -scale;

      BigVecQ3 v0 = tet_centers[0] - tet_centers[3];
      BigVecQ3 v1 = tet_centers[1] - tet_centers[3];
      BigVecQ3 v2 = tet_centers[2] - tet_centers[3];
      BigVecQ3 w_tgt = target - tet_centers[3];
      BigRat den = BigVecQ3::Det(v0, v1, v2);
      BigRat l0 = BigVecQ3::Det(w_tgt, v1, v2) / den;
      BigRat l1 = BigVecQ3::Det(v0, w_tgt, v2) / den;
      BigRat l2 = BigVecQ3::Det(v0, v1, w_tgt) / den;
      BigRat l3 = BigRat(1) - l0 - l1 - l2;
      if (l0 < 0 || l1 < 0 || l2 < 0 || l3 < 0) {
        bary_ok = false;
        break;
      }
    }
    std::cout << "c = " << c_cand << " barycentricValid: " << (bary_ok ? "PASS" : "FAIL") << "\n";
  }

  return 0;
}


