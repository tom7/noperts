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
  BigVecQ3 u0 = center0 / ax0.B;
  vec3 u0_v = {u0.x.ToDouble(), u0.y.ToDouble(), u0.z.ToDouble()};

  ContactInfo core[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(14, 15, 15, 19, 400, 15)
  };
  AxisCertificate ax_core;
  BigVecQ3 ctr_core;
  BigRat del_core;
  Tube229::AuditAxis(tri, core, &ax_core, &ctr_core, &del_core, &err, BigRat(0));
  vec3 v_core = {ctr_core.x.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.y.ToDouble() / ax_core.B.ToDouble(),
                 ctr_core.z.ToDouble() / ax_core.B.ToDouble()};

  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<BigVecQ3> good_centers;
  std::vector<vec3> g_v;
  std::vector<int> good_idx;
  for (size_t i = 0; i < axes500.size(); i++) {
    if (axes500[i].cert.B > 0) {
      BigVecQ3 c = axes500[i].center / axes500[i].cert.B;
      double len = std::sqrt(BigVecQ3::Dot(c, c).ToDouble());
      if (len > 0.01) {
        good_centers.push_back(c);
        g_v.push_back({c.x.ToDouble(), c.y.ToDouble(), c.z.ToDouble()});
        good_idx.push_back(i);
      }
    }
  }

  std::cout << "Testing pairs/triplets of complement axes against v_core...\n";
  int N = 50000;
  std::vector<vec3> pts(N);
  for (int i = 0; i < N; i++) {
    double z = 1.0 - (2.0 * i + 1.0) / N;
    double r = std::sqrt(std::max(0.0, 1.0 - z * z));
    double phi = i * 2.399963229728653;
    pts[i] = {r * std::cos(phi), r * std::sin(phi), z};
  }

  // Precompute dots with pts:
  std::vector<std::vector<float>> dot_p(g_v.size(), std::vector<float>(N));
  for (size_t i = 0; i < g_v.size(); i++) {
    for (int p = 0; p < N; p++) {
      dot_p[i][p] = yocto::dot(pts[p], g_v[i]);
    }
  }
  std::vector<float> core_dots(N);
  for (int p = 0; p < N; p++) {
    core_dots[p] = yocto::dot(pts[p], v_core);
  }

  double box_c = 0.005;
  int found = 0;
  for (size_t i = 0; i < g_v.size(); i++) {
    for (size_t j = i + 1; j < g_v.size(); j++) {
      for (size_t k = j + 1; k < g_v.size(); k++) {
        // Quick check: does {u0, i, j, k} enclose 0?
        // Check if origin is inside:
        vec3 v1 = g_v[i] - u0_v;
        vec3 v2 = g_v[j] - u0_v;
        vec3 v3 = g_v[k] - u0_v;
        double d = yocto::dot(v1, yocto::cross(v2, v3));
        if (std::abs(d) < 1e-6) continue;
        vec3 neg_u0 = -u0_v;
        double l1 = yocto::dot(neg_u0, yocto::cross(v2, v3)) / d;
        double l2 = yocto::dot(v1, yocto::cross(neg_u0, v3)) / d;
        double l3 = yocto::dot(v1, yocto::cross(v2, neg_u0)) / d;
        double l0 = 1.0 - l1 - l2 - l3;
        if (l0 <= 0.01 || l1 <= 0.01 || l2 <= 0.01 || l3 <= 0.01) continue;

        // Origin is strictly inside with margin!
        // Now check if wherever u1, u2, u3 < box_c, core_dots >= 0.001:
        bool ok = true;
        double min_core_fail = 1e9;
        for (int p = 0; p < N; p++) {
          if (dot_p[i][p] < box_c && dot_p[j][p] < box_c && dot_p[k][p] < box_c) {
            if (core_dots[p] < 0.0005) {
              ok = false;
              break;
            }
            if (core_dots[p] < min_core_fail) min_core_fail = core_dots[p];
          }
        }
        if (ok) {
          found++;
          std::cout << "FOUND WINNING COMBO! axes (" << good_idx[i] << ", " << good_idx[j] << ", " << good_idx[k]
                    << "): min_core_fail = " << min_core_fail << "\n";
          // Check exact tetrahedron radius:
          BigVecQ3 tet[4] = {u0, good_centers[i], good_centers[j], good_centers[k]};
          BigRat r_exact = Tube229::ExactTetrahedronAxisRadius(tet);
          std::cout << "  Exact inradius: " << r_exact.ToDouble() << "\n";
          if (found >= 5) goto done;
        }
      }
    }
  }
done:
  if (found == 0) {
    std::cout << "No 3-axis combination satisfied core_dots >= 0.0005 on fail set.\n";
  }
  return 0;
}
