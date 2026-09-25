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

  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Auditing and filtering zero-defect axes...\n";
  std::vector<BigVecQ3> good_centers;
  std::vector<int> good_idx;
  for (size_t i = 0; i < axes500.size(); i++) {
    if (axes500[i].cert.B > 0) {
      BigVecQ3 c = axes500[i].center / axes500[i].cert.B;
      double len = std::sqrt(BigVecQ3::Dot(c, c).ToDouble());
      if (len > 0.01) {
        good_centers.push_back(c);
        good_idx.push_back(i);
      }
    }
  }

  std::cout << "Found " << good_centers.size() << " zero-defect axes with len > 0.01\n";

  // Search for the 3 zero-defect axes that maximize the inradius with u0:
  double best_inrad = 0.0;
  int best_i = -1, best_j = -1, best_k = -1;

  // Quick geometric filter:
  vec3 u0_v = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};
  std::vector<vec3> g_v;
  for (const auto &c : good_centers) {
    g_v.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
  }

  // To search efficiently among good_centers:
  // Random sampling or greedy selection:
  for (size_t i = 0; i < g_v.size(); i++) {
    for (size_t j = i + 1; j < g_v.size(); j++) {
      vec3 normal = yocto::cross(g_v[i], g_v[j]);
      if (yocto::length(normal) < 1e-4) continue;
      for (size_t k = j + 1; k < g_v.size(); k++) {
        // Test tetrahedron:
        BigVecQ3 tet[4] = {u0, good_centers[i], good_centers[j], good_centers[k]};
        // Check if origin is inside:
        BigVecQ3 v1 = tet[1] - tet[0];
        BigVecQ3 v2 = tet[2] - tet[0];
        BigVecQ3 v3 = tet[3] - tet[0];
        BigRat d = BigVecQ3::Det(v1, v2, v3);
        if (d == 0) continue;
        BigVecQ3 neg_u0 = BigVecQ3{BigRat(0), BigRat(0), BigRat(0)} - tet[0];
        BigRat l1 = BigVecQ3::Det(neg_u0, v2, v3) / d;
        BigRat l2 = BigVecQ3::Det(v1, neg_u0, v3) / d;
        BigRat l3 = BigVecQ3::Det(v1, v2, neg_u0) / d;
        BigRat l0 = BigRat(1) - l1 - l2 - l3;
        if (l0 > 0 && l1 > 0 && l2 > 0 && l3 > 0) {
          BigRat r = Tube229::ExactTetrahedronAxisRadius(tet);
          double rd = r.ToDouble();
          if (rd > best_inrad) {
            best_inrad = rd;
            best_i = i; best_j = j; best_k = k;
            std::cout << "New best inradius: " << best_inrad
                      << " (axes " << good_idx[i] << ", " << good_idx[j] << ", " << good_idx[k] << ")\n";
          }
        }
      }
    }
  }

  std::cout << "\nGLOBAL MAXIMUM INRADIUS FOUND: " << best_inrad << "\n";
  return 0;
}
